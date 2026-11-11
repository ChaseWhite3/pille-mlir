#lang racket/base

(require json
         racket/list
         racket/match
         racket/port
         racket/string
         racket/treelist
         "semantics.rkt")

(provide type_is attribute_is any_constraint any_of all_of parametric same
         type_def attribute_def operation_def make_dialect
         constraint_serialize constraint_deserialize
         member_serialize member_deserialize
         dialect_serialize dialect_deserialize
         operation_name operation_names
         smt_operation_names operation_models unmodeled_operation_names
         sem_operand sem_result sem_local
         sem_const_width sem_const_like sem_binary sem_select
         make_semantics semantic_error_node
         (rename-out [constraint? is_constraint]
                     [member? is_member]
                     [dialect? is_dialect]
                     [is_semantic_expression is_semantic_expression]
                     [is_semantics is_semantics]
                     [dialect-name dialect_name]
                     [dialect-irdl dialect_irdl]))

;; These immutable descriptions are shared by macro expansion and runtime code.
;; The emitter deliberately does not intern equal constraints: every occurrence
;; gets its own IRDL variable unless `same` explicitly asks for equality.
(struct constraint (tag args) #:transparent)
(struct member (kind name groups semantics) #:transparent)
(struct dialect (name members irdl) #:transparent)

(define (schema-error who message . arguments)
  (apply raise-user-error who message arguments))

(define (items who value)
  (cond
    [(treelist? value) (treelist->list value)]
    [(list? value) value]
    [else (raise-argument-error who "list or treelist" value)]))

(define (identifier who value)
  (unless (and (string? value)
               (regexp-match? #px"^[A-Za-z_][A-Za-z0-9_]*$" value))
    (raise-argument-error who "identifier string ([A-Za-z_][A-Za-z0-9_]*)" value))
  (string->immutable-string value))

(define (irdl-identifier who value)
  (define checked (identifier who value))
  (unless (and (regexp-match? #px"^[a-z][a-z0-9_]*$" checked)
               (not (string-contains? checked "__")))
    (schema-error who
                  "invalid IRDL name ~s: use lowercase letters, digits, and single underscores, starting with a letter"
                  checked))
  checked)

;; An operation's attributes are entries of a dictionary keyed by string, so
;; MLIR's customary dotted keys ("dialect.key") are allowed there. Each segment
;; follows the same rules as any other name in the schema.
(define (attribute-name who value)
  (unless (and (string? value) (non-empty-string? value))
    (raise-argument-error who "attribute name string" value))
  (for ([segment (in-list (string-split value "." #:trim? #f))])
    (irdl-identifier who segment))
  (string->immutable-string value))

(define (literal who value)
  ;; MLIR owns the full literal grammar, including dialect-specific syntax.
  ;; Keep literal text on its own line, but leave parsing to Module's verifier.
  (unless (and (string? value)
               (not (string=? (string-trim value) ""))
               (not (for/or ([character (in-string value)])
                      (memv character '(#\return #\newline #\nul)))))
    (raise-argument-error who "nonempty, single-line MLIR literal string" value))
  (string->immutable-string (string-trim value)))

(define (type_is text)
  (constraint 'type-is (list (literal 'type_is text))))

(define (attribute_is text)
  (constraint 'attribute-is (list (literal 'attribute_is text))))

(define (any_constraint)
  (constraint 'any '()))

(define (constraints who values)
  (define result (items who values))
  (for ([value (in-list result)])
    (unless (constraint? value)
      (raise-argument-error who "list or treelist of constraints" values)))
  result)

(define (combination who tag values)
  (define children (constraints who values))
  (when (null? children)
    (schema-error who "expected at least one constraint"))
  (constraint tag children))

(define (any_of values) (combination 'any_of 'any-of values))
(define (all_of values) (combination 'all_of 'all-of values))

(define (parametric kind namespace name parameters)
  (define kind-name (if (symbol? kind) (symbol->string kind) kind))
  (unless (or (equal? kind-name "type") (equal? kind-name "attribute"))
    (raise-argument-error 'parametric "'type or 'attribute (symbol or string)" kind))
  (constraint 'parametric
              (list (string->immutable-string kind-name)
                    (and namespace (irdl-identifier 'parametric namespace))
                    (irdl-identifier 'parametric name)
                    (constraints 'parametric parameters))))

(define (same name value)
  (unless (constraint? value)
    (raise-argument-error 'same "constraint" value))
  (constraint 'same (list (identifier 'same name) value)))

(define (named-constraints who values [check-name irdl-identifier])
  (define seen (make-hash))
  (for/list ([entry (in-list (items who values))])
    (match (items who entry)
      [(list name value)
       (define checked-name (check-name who name))
       (unless (constraint? value)
         (raise-argument-error who "named constraint [name, constraint]" entry))
       (when (hash-has-key? seen checked-name)
         (schema-error who "duplicate parameter or port name: ~a" checked-name))
       (hash-set! seen checked-name #t)
       (list checked-name value)]
      [_ (raise-argument-error who "named constraint [name, constraint]" entry)])))

(define (type_def name parameters)
  (member "type" (irdl-identifier 'type_def name)
          (list (named-constraints 'type_def parameters))
          #f))

(define (attribute_def name parameters)
  (member "attribute" (irdl-identifier 'attribute_def name)
          (list (named-constraints 'attribute_def parameters))
          #f))

;; Attribute constraints may also describe TypeAttr values. Only operands and
;; results require type-valued constraints; type/attribute parameters are general.
(define (type-compatible? value)
  (match value
    [(constraint 'attribute-is _) #f]
    [(constraint 'parametric (list kind _ _ _)) (equal? kind "type")]
    [(constraint 'same (list _ child)) (type-compatible? child)]
    [(constraint (or 'any-of 'all-of) children)
     (andmap type-compatible? children)]
    [_ #t]))

(define (type-ports who values)
  (define ports (named-constraints who values))
  (for ([port (in-list ports)])
    (unless (type-compatible? (cadr port))
      (schema-error who "operand/result ~a requires a type constraint" (car port))))
  ports)

;; The builtin types a constraint admits: a list of MLIR type texts, or #f when
;; the constraint is unbounded. Custom dialect types and attributes are never
;; builtin integers, so they contribute nothing.
(define (constraint-types value)
  (match value
    [(constraint 'type-is (list text)) (list text)]
    [(constraint 'any _) #f]
    [(constraint (or 'attribute-is 'parametric) _) '()]
    [(constraint 'same (list _ child)) (constraint-types child)]
    [(constraint 'any-of children)
     (define sets (map constraint-types children))
     (and (andmap values sets) (remove-duplicates (append* sets)))]
    [(constraint 'all-of children)
     (define sets (filter values (map constraint-types children)))
     (and (pair? sets)
          (for/fold ([result (car sets)]) ([other (in-list (cdr sets))])
            (filter (lambda (text) (and (memf (lambda (candidate) (equal? candidate text)) other) #t))
                    result)))]))

;; Ports whose top-level constraint is the same shared variable always have
;; equal types. Any other port is its own equality class: equal-looking
;; constraints stay independent, exactly as in the generated IRDL.
(define (semantic-ports entries)
  (for/list ([entry (in-list entries)])
    (define types (constraint-types (cadr entry)))
    (port (car entry)
          (match (cadr entry)
            [(constraint 'same (list key _)) (cons 'same key)]
            [_ (cons 'port (car entry))])
          (and types (filter-map type->width types)))))

(define (operation_def name operands results [attributes '()] [semantics #f])
  (define checked-name (irdl-identifier 'operation_def name))
  (define checked-operands (type-ports 'operation_def operands))
  (define checked-results (type-ports 'operation_def results))
  (for ([port (in-list checked-results)])
    (when (assoc (car port) checked-operands)
      (schema-error 'operation_def "duplicate operand/result name: ~a" (car port))))
  (define checked-attributes (named-constraints 'operation_def attributes attribute-name))
  (when semantics
    (unless (is_semantics semantics)
      (raise-argument-error 'operation_def "SMT semantics or #f" semantics))
    ;; The model cannot observe attributes. Accepting both would let an
    ;; attribute carry meaning that every proof silently ignores.
    (unless (null? checked-attributes)
      (schema-error 'operation_def
                    "~a: conflicting clauses: SMT semantics cannot be attached to an operation with required attributes (attribute-dependent semantics are unsupported)"
                    checked-name))
    (check-semantics checked-name semantics
                     (semantic-ports checked-operands) (semantic-ports checked-results)))
  (member "operation" checked-name
          (list checked-operands checked-results checked-attributes)
          semantics))

(define (member-constraints definition)
  (for*/list ([group (in-list (member-groups definition))]
              [entry (in-list group)])
    (cadr entry)))

;; Match the runtime loader's getBases/checkCorrectAnyOf restrictions. A branch
;; is unbounded (#f) or has a set of referenced IRDL definitions. Literal `is`
;; constraints are bounded, but cannot refer to these dynamic definitions.
;; all_of deliberately uses only its first child, as MLIR's loader does:
;; https://mlir.llvm.org/doxygen/IRDLLoading_8cpp_source.html
(define (constraint-bases namespace value)
  (match value
    [(constraint 'any _) #f]
    [(constraint (or 'type-is 'attribute-is) _) '()]
    [(constraint 'same (list _ child)) (constraint-bases namespace child)]
    [(constraint 'parametric (list _ target-namespace name _))
     (list (cons (or target-namespace namespace) name))]
    [(constraint 'all-of children) (constraint-bases namespace (car children))]
    [(constraint 'any-of children)
     (define bases (map (lambda (child) (constraint-bases namespace child)) children))
     (and (andmap values bases) (remove-duplicates (append* bases)))]))

(define (validate-any-of namespace definition members children)
  (define seen (make-hash))
  (for ([child (in-list children)])
    (define bases (constraint-bases namespace child))
    (unless bases
      (schema-error 'make_dialect
                    "~a: any_of alternative has an unbounded any constraint and cannot be loaded at runtime; use any without a union, or put a bounded constraint first in all_of"
                    (member-name definition)))
    (for ([base (in-list bases)])
      (when (hash-has-key? seen base)
        (define target (hash-ref members (cdr base)))
        (define kind (member-kind target))
        (define arity (length (car (member-groups target))))
        (define example
          (if (and (equal? kind "type") (= arity 1))
              (format "type_ref(~s, i32 || i64)" (cdr base))
              (format "~a_ref(~s~a)"
                      (if (equal? kind "attribute") "attr" "type")
                      (cdr base) (if (zero? arity) "" ", ..."))))
        (schema-error 'make_dialect
                      "~a: any_of alternatives share parametric base ~a.~a and cannot be loaded at runtime; move parameter alternatives inside one reference, for example ~a"
                      (member-name definition) (car base) (cdr base) example))
      (hash-set! seen base #t))))

(define (validate-member namespace definition members)
  (define shared (make-hash))
  (define (visit value)
    (match value
      [(constraint 'same (list name child))
       (define previous (hash-ref shared name #f))
       (when (and previous (not (equal? previous child)))
         (schema-error 'make_dialect
                       "~a: equality variable ~a has conflicting constraints"
                       (member-name definition) name))
       (hash-set! shared name child)
       (visit child)]
      [(constraint 'parametric (list kind requested-namespace name parameters))
       (define target-namespace (or requested-namespace namespace))
       (unless (equal? target-namespace namespace)
         (schema-error 'make_dialect
                       "~a: reference ~a.~a is outside this dialect; expected ~a"
                       (member-name definition) target-namespace name namespace))
       (define target (hash-ref members name #f))
       (unless target
         (schema-error 'make_dialect "~a: unknown ~a reference: ~a.~a"
                       (member-name definition) kind namespace name))
       (unless (equal? (member-kind target) kind)
         (schema-error 'make_dialect "~a: ~a.~a is a ~a, expected a ~a"
                       (member-name definition) namespace name (member-kind target) kind))
       (define arity (length (car (member-groups target))))
       (unless (= arity (length parameters))
         (schema-error 'make_dialect
                       "~a: ~a.~a expects ~a parameters, received ~a"
                       (member-name definition) namespace name arity (length parameters)))
       (for-each visit parameters)]
      [(constraint 'any-of children)
       ;; Validate children even when their bases are hidden behind parametric
       ;; arguments or a later all_of child: every emitted any_of must load.
       (for-each visit children)
       (validate-any-of namespace definition members children)]
      [(constraint 'all-of children) (for-each visit children)]
      [_ (void)]))
  (for-each visit (member-constraints definition)))

(define (emit-member namespace definition)
  (define lines '())
  (define next-id 0)
  (define shared (make-hash))
  (define (line text) (set! lines (cons (string-append "      " text) lines)))
  (define (instruction body)
    (define variable (format "%c~a" next-id))
    (set! next-id (add1 next-id))
    (line (format "~a = ~a" variable body))
    variable)
  (define (emit value)
    (match value
      [(constraint (or 'type-is 'attribute-is) (list text))
       (instruction (string-append "irdl.is " text))]
      [(constraint 'any _) (instruction "irdl.any")]
      [(constraint (and tag (or 'any-of 'all-of)) children)
       (define arguments (map emit children))
       (instruction (format "irdl.~a(~a)"
                            (if (eq? tag 'any-of) "any_of" "all_of")
                            (string-join arguments ", ")))]
      [(constraint 'parametric (list _ target-namespace name parameters))
       (define arguments (map emit parameters))
       (instruction (format "irdl.parametric @~a::@~a<~a>"
                            (or target-namespace namespace) name
                            (string-join arguments ", ")))]
      [(constraint 'same (list name child))
       (hash-ref! shared name (lambda () (emit child)))]))
  (define groups (member-groups definition))
  ;; Emit all constraints before signatures, in declaration and port order.
  (define variables
    (for/list ([group (in-list groups)])
      (for/list ([entry (in-list group)])
        (list (car entry) (emit (cadr entry))))))
  (define (signature operation entries)
    (line (format "irdl.~a(~a)" operation
                  (string-join (for/list ([entry (in-list entries)])
                                 (format "~a: ~a" (car entry) (cadr entry)))
                               ", "))))
  (cond
    [(equal? (member-kind definition) "operation")
     (signature "operands" (car variables))
     (signature "results" (cadr variables))
     (unless (null? (caddr variables))
       (line (format "irdl.attributes {~a}"
                     (string-join
                      (for/list ([entry (in-list (caddr variables))])
                        (format "\"~a\" = ~a" (car entry) (cadr entry))) ", "))))]
    [else (signature "parameters" (car variables))])
  (string-append "    irdl." (member-kind definition) " @" (member-name definition) " {\n"
                 (string-join (reverse lines) "\n") "\n    }"))

(define (make_dialect name definitions)
  (define namespace (irdl-identifier 'make_dialect name))
  (define members (items 'make_dialect definitions))
  (define by-name (make-hash))
  (for ([definition (in-list members)])
    (unless (member? definition)
      (raise-argument-error 'make_dialect "list or treelist of dialect members" definitions))
    (when (hash-has-key? by-name (member-name definition))
      (schema-error 'make_dialect "duplicate dialect member: ~a" (member-name definition)))
    (hash-set! by-name (member-name definition) definition))
  (for ([definition (in-list members)])
    (validate-member namespace definition by-name))
  (dialect namespace members
           (string->immutable-string
            (string-append
             "module {\n  irdl.dialect @" namespace " {\n"
             (string-join (map (lambda (definition) (emit-member namespace definition)) members)
                          "\n\n")
             (if (null? members) "" "\n")
             "  }\n}\n"))))

(define (check-dialect who value)
  (unless (dialect? value) (raise-argument-error who "dialect" value)))

(define (operation_name value local-name)
  (check-dialect 'operation_name value)
  (define name (irdl-identifier 'operation_name local-name))
  (unless (for/or ([definition (in-list (dialect-members value))])
            (and (equal? (member-kind definition) "operation")
                 (equal? (member-name definition) name)))
    (schema-error 'operation_name "unknown operation: ~a.~a" (dialect-name value) name))
  (string->immutable-string (string-append (dialect-name value) "." name)))

(define (qualified-names value keep?)
  (for/list ([definition (in-list (dialect-members value))]
             #:when (and (equal? (member-kind definition) "operation") (keep? definition)))
    (string->immutable-string
     (string-append (dialect-name value) "." (member-name definition)))))

(define (operation_names value)
  (check-dialect 'operation_names value)
  (list->treelist (qualified-names value (lambda (_definition) #t))))

(define (smt_operation_names value)
  (check-dialect 'smt_operation_names value)
  (list->treelist (qualified-names value member-semantics)))

;; Operations without a model are named explicitly so that the lowering pass can
;; report a missing model instead of an unknown operation.
(define (unmodeled_operation_names value)
  (check-dialect 'unmodeled_operation_names value)
  (qualified-names value (lambda (definition) (not (member-semantics definition)))))

;; The models are read from this dialect value. There is no registry keyed by
;; operation name: two dialect values may give one name different meanings.
(define (operation_models value)
  (check-dialect 'operation_models value)
  (for/list ([definition (in-list (dialect-members value))]
             #:when (member-semantics definition))
    (cons (string-append (dialect-name value) "." (member-name definition))
          (semantics->manifest (member-semantics definition)
                               (map car (car (member-groups definition)))))))

;; JSON arrays provide a portable, inert expansion-time representation. Decoders
;; rebuild through the public constructors instead of trusting serialized tags.
(define (constraint->data value)
  (match value
    [(constraint (and tag (or 'type-is 'attribute-is)) (list text))
     (list (symbol->string tag) text)]
    [(constraint 'any _) '("any")]
    [(constraint (and tag (or 'any-of 'all-of)) children)
     (list (symbol->string tag) (map constraint->data children))]
    [(constraint 'parametric (list kind namespace name parameters))
     (list "parametric" kind namespace name (map constraint->data parameters))]
    [(constraint 'same (list name child))
     (list "same" name (constraint->data child))]))

(define (data->constraint value)
  (match value
    [(list "type-is" text) (type_is text)]
    [(list "attribute-is" text) (attribute_is text)]
    [(list "any") (any_constraint)]
    [(list "any-of" (? list? children)) (any_of (map data->constraint children))]
    [(list "all-of" (? list? children)) (all_of (map data->constraint children))]
    [(list "parametric" kind namespace name (? list? parameters))
     (parametric kind namespace name (map data->constraint parameters))]
    [(list "same" name child) (same name (data->constraint child))]
    [_ (schema-error 'constraint_deserialize "invalid serialized constraint")]))

(define (group->data group)
  (for/list ([entry (in-list group)])
    (list (car entry) (constraint->data (cadr entry)))))

(define (data->group value)
  (unless (list? value) (schema-error 'member_deserialize "invalid serialized port list"))
  (for/list ([entry (in-list value)])
    (match entry
      [(list name child) (list name (data->constraint child))]
      [_ (schema-error 'member_deserialize "invalid serialized named constraint")])))

(define (member->data value)
  (append (list (member-kind value) (member-name value))
          (map group->data (member-groups value))
          (if (equal? (member-kind value) "operation")
              (list (if (member-semantics value)
                        (semantics->data (member-semantics value))
                        (json-null)))
              '())))

;; Version 1 operations have no semantics field. Version 2 operations always
;; have one, which is null for a schema-only declaration.
(define (data->member version value)
  (match* (version value)
    [(_ (list "type" name parameters)) (type_def name (data->group parameters))]
    [(_ (list "attribute" name parameters)) (attribute_def name (data->group parameters))]
    [(1 (list "operation" name operands results attributes))
     (operation_def name (data->group operands) (data->group results) (data->group attributes))]
    [(2 (list "operation" name operands results attributes semantics))
     (operation_def name (data->group operands) (data->group results) (data->group attributes)
                    (and (not (eq? semantics (json-null))) (data->semantics semantics)))]
    [(_ _) (schema-error 'member_deserialize "invalid serialized dialect member")]))

;; Version 2 added optional SMT semantics to operations. Version 1 descriptors
;; remain readable; new descriptors are always written as version 2.
(define schema-version 2)

(define (serialize tag value)
  (string->immutable-string (jsexpr->string (list "pille-irdl" schema-version tag value))))

(define (deserialize who tag text)
  (unless (string? text) (raise-argument-error who "string?" text))
  (define input (open-input-string text))
  (define data
    (with-handlers ([exn:fail:read? (lambda (_error) (schema-error who "invalid serialized JSON"))])
      (read-json input)))
  (unless (regexp-match? #px"^\\s*$" (port->string input))
    (schema-error who "unexpected trailing content after serialized JSON"))
  (match data
    [(list "pille-irdl" (and version (or 1 2)) (== tag) value) (values version value)]
    [_ (schema-error who "invalid serialized ~a or unsupported schema version" tag)]))

(define (constraint_serialize value)
  (unless (constraint? value) (raise-argument-error 'constraint_serialize "constraint" value))
  (serialize "constraint" (constraint->data value)))

(define (constraint_deserialize text)
  (define-values (_version data) (deserialize 'constraint_deserialize "constraint" text))
  (data->constraint data))

(define (member_serialize value)
  (unless (member? value) (raise-argument-error 'member_serialize "dialect member" value))
  (serialize "member" (member->data value)))

(define (member_deserialize text)
  (define-values (version data) (deserialize 'member_deserialize "member" text))
  (data->member version data))

(define (dialect_serialize value)
  (check-dialect 'dialect_serialize value)
  (serialize "dialect" (list (dialect-name value) (map member->data (dialect-members value)))))

(define (dialect_deserialize text)
  (define-values (version data) (deserialize 'dialect_deserialize "dialect" text))
  (match data
    [(list name (? list? definitions))
     (make_dialect name (for/list ([definition (in-list definitions)])
                          (data->member version definition)))]
    [_ (schema-error 'dialect_deserialize "invalid serialized dialect")]))

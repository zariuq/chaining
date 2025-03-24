;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Examples of both backward and forward curried chainers.             ;;
;;                                                                     ;;
;; The curried forward chainer relies on the curried backward chainer  ;;
;; to unfold the rules.                                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;
;; Nat ;;
;;;;;;;;;

;; Define Nat
(: Nat Type)
(: Z Nat)
(: S (-> Nat Nat))

;; Define cast functions between Nat and Number
(: fromNumber (-> Number Nat))
(= (fromNumber $n) (if (<= $n 0) Z (S (fromNumber (- $n 1)))))
(: fromNat (-> Nat Number))
(= (fromNat Z) 0)
(= (fromNat (S $k)) (+ 1 (fromNat $k)))

(= (minNat $x $y)
  (let $nx (fromNat $x)
    (let $ny (fromNat $y)
      (let $nm ((py-atom min) $nx $ny)
        (fromNumber $nm)))))

;;;;;;;;;;;;;;;;;;;;
;; Knowledge base ;;
;;;;;;;;;;;;;;;;;;;;

;; Simple knowledge base for expository purpose.  Do not confuse `->`,
;; the MeTTa arrow type, and `→`, a regular MeTTa symbol denoting a
;; relationship.

!(bind! &kb (new-space))

!(add-atom &kb (: a A))
!(add-atom &kb (: ab (→ A B)))
!(add-atom &kb (: bc (→ B C)))
!(add-atom &kb (: ModusPonens
                  (-> (→ $p $q)           ; Premise 1
                      (-> $p              ; Premise 2
                          $q))))          ; Conclusion


;;;;;;;;;;;;;;;;;;;;;;
;; Backward chainer ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Curried Backward Chainer.  The arguments of the backward chainer
;; are:
;;
;; * Knowledge base: pointer to a space containing axioms and rules in
;;   the format (: <NAME> <RULE>).  Note that rules are explicitely
;;   curried, meaning that a rule with two premises is represented by
;;
;;   (: <NAME> (-> <PREMISE1> (-> <PREMISE2> <CONCLUSION>)))
;;
;; * Query: a metta term of the form (: <PROOF> <THEOREM>) where
;;   <PROOF> and <THEOREM> may contain free variables that may be
;;   filled by the backward chainer.
;;
;; * Maximum depth: maximum depth of the generated proof tree.
;;
;; A result is the query with its variables grounded, fully or
;; partially.  If multiple results are possible, they are returned as
;; a superposition.
; (: bc (-> $a                            ; Knowledge base space
;           Nat                           ; Maximum depth
;           $b                            ; Query
;           $b))                          ; Result
; ;; Base case
; (= (bc $kb $_ (: $prf $ccln)) (match $kb (: $prf $ccln) (: $prf $ccln)))
; ;; Recursive step
; (= (bc $kb (S $k) (: ($prfabs $prfarg) $ccln))
;    (let* (((: $prfabs (-> $prms $ccln)) (bc $kb $k (: $prfabs (-> $prms $ccln))))
;           ((: $prfarg $prms) (bc $kb $k (: $prfarg $prms))))
;      (: ($prfabs $prfarg) $ccln)))

(: bc (-> $kb          ; Knowledge base space
          Nat          ; Maximum depth
          $goal        ; Query
          $goal))      ; Result

;; Base case
(= (bc $kb $_ (: $proof $conclusion))
   (match $kb (: $proof $conclusion) (: $proof $conclusion)))

;; Recursive step
(= (bc $kb (S $k) (: ($rule $arg) $conclusion))
   (let* (
          ((: $rule (-> $premises $conclusion))
            (bc $kb $k (: $rule (-> $premises $conclusion))))

          ((: $arg $premises)
            (bc $kb $k (: $arg $premises)))
         )
     (: ($rule $arg) $conclusion)))


;; Test curried backward chainer
!(assertEqual
  (bc &kb (fromNumber 0) (: $proof A))
  (: a A))
!(assertEqual
  (bc &kb (fromNumber 2) (: $proof B))
  (: ((ModusPonens ab) a) B))
!(assertEqual
  (bc &kb (fromNumber 3) (: $proof C))
  (: ((ModusPonens bc) ((ModusPonens ab) a)) C))
  ; ρ
;;;;;;;;;;;;;;;;;;;;;
;; Forward chainer ;;
;;;;;;;;;;;;;;;;;;;;;

;; Curried Forward Chainer.  The arguments of the forward chainer are:
;;
;; * Knowledge base: pointer to a space containing axioms and rules in
;;   the format (: <NAME> <RULE>).  Note that rules are explicitely
;;   curried, meaning that a rule with two premises is represented by
;;
;;   (: <NAME> (-> <PREMISE1> (-> <PREMISE2> <CONCLUSION>)))
;;
;; * Source: a metta term of the form (: <PROOF> <THEOREM>) where
;;   <PROOF> and <THEOREM> may contain free variables.  Beware that
;;   the source is assumed to be true.  That is especially important
;;   to consider when introducing free variables, because these free
;;   variables will be treated as if they are univerally quantified.
;;
;; * Maximum depth: maximum depth of the generated proof tree.
;;
;; A result is a conclusion that can be reached from the source.  If
;; multiple results are possible, they are returned as a
;; superposition.
; (: fcold (-> $a                            ; Knowledge base space
;           Nat                           ; Maximum depth
;           $b                            ; Source
;           $b))                          ; Conclusion
;; Base case
; (= (fcold $kb $_ (: $prf $prms)) (: $prf $prms))
; ;; Recursive step
; (= (fcold $kb (S $k) (: $prfarg $prms))
;    (let (: $prfabs (-> $prms $ccln)) (bc $kb $k (: $prfabs (-> $prms $ccln)))
;      (fcold $kb $k (: ($prfabs $prfarg) $ccln))))
; (= (fcold $kb (S $k) (: $prfabs (-> $prms $ccln)))
;     (let (: $prfarg $prms) (bc $kb $k (: $prfarg $prms))
;      (fcold $kb $k (: ($prfabs $prfarg) $ccln))))

; ;; This 'new' fc version is added by Zar
; (: fc (-> $a                            ; Knowledge base space
;           Nat                           ; Maximum depth
;           $b                            ; Source
;           $b))                          ; Conclusion

; (= (fc $kb $_ (: $prf $prms)) (: $prf $prms))

; (= (fc $kb (S $k) (: $prfarg $prms))
;    (let (: $prfabs (-> $prms $ccln)) (bc $kb (minNat $k (fromNumber 1)) (: $prfabs (-> $prms $ccln)))
;      (fc $kb $k (: ($prfabs $prfarg) $ccln))))
; (= (fc $kb (S $k) (: $prfabs (-> $prms $ccln)))
;     (let (: $prfarg $prms) (bc $kb (minNat $k (fromNumber 1)) (: $prfarg $prms))
;      (fc $kb $k (: ($prfabs $prfarg) $ccln))))

(: fc (-> $kb         ; Knowledge base space
          Nat         ; Maximum depth
          $goal       ; Source expression
          $goal))     ; Resulting conclusions

;; Base case
(= (fc $kb $_ (: $proof $premises))
   (: $proof $premises))

;; Recursive step #1
(= (fc $kb (S $k) (: $arg $premises))
   (let (: $rule (-> $premises $conclusion))
        (bc $kb $k (: $rule (-> $premises $conclusion)))
     (fc $kb $k (: ($rule $arg) $conclusion))))

;; Recursive step #2
(= (fc $kb (S $k) (: $rule (-> $premises $conclusion)))
   (let (: $arg $premises)
        (bc $kb $k (: $arg $premises))
     (fc $kb $k (: ($rule $arg) $conclusion))))


;; Test curried forward chainer
!(assertEqualToResult
  (fc &kb (fromNumber 1) (: ab (→ A B)))
  ((: ab (→ A B))
   (: (ModusPonens ab) (-> A B))))
!(assertEqualToResult
  (fc &kb (fromNumber 2) (: ab (→ A B)))
  ((: ab (→ A B))
   (: (ModusPonens ab) (-> A B))
   (: ((ModusPonens ab) a) B)))
!(assertEqualToResult
  (fc &kb (fromNumber 3) (: a A))
  ((: a A)
   (: ((ModusPonens ab) a) B)
   (: ((ModusPonens bc) ((ModusPonens ab) a)) C)))

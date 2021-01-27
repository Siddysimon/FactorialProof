; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;;
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(definec acc-fn-sum (x :nat acc :nat) :nat
  (cond ((zp  x)    acc)
        (t        (acc-fn-sum (1- x) (+ x acc)))))

(definec non-acc-fn-sum (x :nat) :nat
  (cond ((zp  x) 0)
        (t       (+ x (non-acc-fn-sum  (1- x))))))

(definec acc-fn-sum-interface (x :nat) :nat
  (acc-fn-sum x 0))

; Sanity check, does test? find any counterexamples? No. :D
(test? (implies (and (natp x) (natp acc) (zp acc))
              (equal (non-acc-fn-sum x) (acc-fn-sum x acc))))

#|
(set-gag-mode nil)
:brr t
(cw-gstack :frames 30)
|#



(definec acc-fn-mult (x :nat acc :nat) :nat
  (cond ((zp  x)    acc)
        (t        (acc-fn-mult (1- x) (* x acc)))))

(definec non-acc-fn-mult (x :nat) :nat
  (cond ((zp  x) 1)
        (t       (* x (non-acc-fn-mult  (1- x))))))

(definec acc-fn-mult-interface (x :nat) :nat
  (acc-fn-mult x 1))

; Sanity check, does test? find any counterexamples? No. :D
(test? (implies (and (natp x) (natp acc) (= 1 acc))
              (equal (non-acc-fn-mult x) (acc-fn-mult x acc))))


#|
Description:
In order to prove mult-associativity-one, we must prove associativity in the
general case for our accumulator function.

That is, adding to the accumulator is the same as adding to the result of the function.
|#


(defthm mult-associativity-general
  (implies (and (natp a) (natp b) (natp c))
           (equal (acc-fn-mult a (* c b))
                  (* b (acc-fn-mult a c)))))

#|
Description:
mult-associativity-one is required to prove a specific case in rec=acc-sum.
In paticular, this handles the case in which c * b = 1, or when acc = 1, which is the base case.
This unwinding of the recursion is required to be explicitly handled as a theorem
for ACL2s to prove rec=acc-sum.
|#

(defthm mult-associativity-one
  (implies (and (natp a) (natp b) (= acc 1))
           (equal (acc-fn-mult a b)
                  (* b (acc-fn-mult a acc)))))

#|
Description:
rec=acc-mult claims that the non-accumulator version of the nth factorial
equals the accumulator version describing the same function for all natural numbers x.

|#
(defthm rec=acc-mult
   (implies (and (natp x))

              (= (non-acc-fn-mult x)
                 (acc-fn-mult-interface x))))

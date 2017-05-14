;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; This file contains the code for the Resoltuion Theorem Prover COS470 Assignment.
;;;;; The document contains a series of functions designed to complete specific tasks
;;;;; as defined by the problem assignment. 
;;;;; Created: 3/30/2017
;;;;; Authors: Stanley C. Small <stanley.small1@maine.edu>
;;;;; Modifications: none
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "unify.lisp")

;;; This is an axiom set for the Marcus domain (renaimed Maximus because I was trying to 
;;;	be clever). The axioms are input in clause form with declarations and implications. 
;;;	EX. (human Maximus) declares that Maximus is human
;;; (or (not (human ?x1)) (mortal ?x1)) is the same as ~human or mortal, indicating that 
;;;	if one is human, he is also mortal. Literals with computable predicates such as 
;;; (gt (- ?t2 ?t1) 150) exist in the axiom set and are defined below. Variables can be 
;;;	declared such as (defvar now 2017). 

(setq Maxioms '(
	(human Maximus)
	(Pompeian Maximus)
	(born Maximus 40)
	(erupted volcano 79)
	(or (not (human ?x1)) 
		(mortal ?x1))
	(or (not (Pompeian ?x2))
		(died ?x2 79))
	(or (not (mortal ?x3))
		(not (born ?x3 ?t1))
		(not (gt (- ?t2 ?t1) 150))
		(dead ?x3 ?t2))
	(or (not (alive ?x4 ?t3))
		(not (dead ?x4 ?t3)))
	(or (dead ?x5 ?t4)
		(alive ?x5 ?t4))
	(or (not (died ?x6 ?t5))
		(not (gt ?t6 ?t5))
		(dead ?x6 ?t6))))

(defvar now 2017)
(defun gt (x y)
	(> x y))

;;; This is an axiom set for the Jack world. There is a dog Fido and a cat Puss. Jack 
;;;	owns Fido. A cat is an animal. Someone who owns a dog is an animal lover. A lover of 
;;;	animals cannot kill another animal. 

(setq Jaxioms '(
	(cat Puss) 
	(dog Fido)
	(owns Jack Fido)
	(or (not (cat ?u)) 
		(animal ?u))
	(or (not (dog ?y)) 
		(not (owns ?x ?y)) 
		(animallover ?x))
	(or (not (animallover ?z)) 
		(not (animal ?w)) 
		(not (kills ?z ?w))))) 

;;;
;;; Function: getliterals
;;; Arguments:  
;;;    - x: a theorem or axiom set
;;; Returns: a list of literals 
;;; Description:
;;;     This function takes a statement in clause form and returns a list of literals.
;;;		EX. (or (not (cat ?u)) (animal ?u)) -> ((not (cat ?u)) (animal ?u)).
;;;		The function removes OR if within the statement or makes a list. 
;;;

(defun getliterals (x)
	(if (eql (car x) 'or) (cdr (loop for i in x collect i)) (list x)))

;;;
;;; Function: addor
;;; Arguments:  
;;;    - x: a theorem or axiom set
;;; Returns: a list of literals with or preceeding them
;;; Description:
;;;     This function takes a list of literals and returns a statement in clause form.
;;;		EX.  ((not (cat ?u)) (animal ?u)) -> (or (not (cat ?u)) (animal ?u))
;;;		The function adds OR if within the statement or does nothing.
;;;

(defun addor (x)
	(if (<= (length x) 1) (car x) (cons 'OR x)))

;;;
;;; Function: negate
;;; Arguments:  
;;;    - x: a literal
;;; Returns: a negated literal
;;; Description:
;;;     This function negates a literal. 
;;;		EX.  (not (cat ?u)) -> (cat ?u)
;;;		EX.  (cat ?u) -> (not (cat ?u))
;;;

(defun negate (x)
	(if (eql (car x) 'not) (cadr x) (cons 'not (list x))))

;;;
;;; Function: resolve
;;; Arguments:  
;;;    - thm: a theorem
;;;	   - ax:  an axiom
;;; Returns: a resolved statment
;;; Description:
;;;     This function resolves an axiom with another statment (theorem).
;;;		EX.  (human marus) (or (not (human ?x1)) (mortal ?x1)) -> (mortal ?x1)    
;;;

(defun resolve (thm ax)
  	(let (res)												;; resolvent
  	(setq res (append (getliterals ax) (getliterals thm)))	;; list of literals
  	(loop for i in (getliterals ax)							;; loop through statements
    	do (loop for k in (getliterals thm)
      		do (if (equal (negate k) i) 
		      	(progn 
		      		(setq res 
		      			(remove i res :test #'equal)) 		;; remove negations
		          	(setq res 
		          		(remove k res :test #'equal))))))
		  (addor res)))										;; add 'OR

;;;
;;; Function: compute
;;; Arguments:  
;;;	   - ax:  an axiom
;;; Returns: a axiom with computed predicates
;;; Description:
;;;     This function computes literals with computable predicates. 
;;;		EX.  (not (gt (- NOW 40) 150)) -> nil
;;;		     
;;;

(defun compute (ax)
	(let (com)												;; computed axiom
	(loop for i in (getliterals ax)
		do (if (or 	(ignore-errors (eval i)) 				;; if literal or
					(ignore-errors (eval (negate i)))) 		;; negated literal
						(setq com (push (eval i) com))		;; evaluates to t
						(setq com (push i com))))			;; evaluate literal
		(addor com)))										;; add 'OR

;;;
;;; Function: rtp
;;; Arguments:  
;;;	   - thm:  a theorem
;;;	   - bind:   bindings
;;;	   - ax:   an axiom set
;;;	   - thms:  a list of theorems used to check if the program has failed
;;; Returns: 'SUCCESS or 'FAILURE
;;; Description:
;;;     This is the main RTP function of the program. It is passed in a theorem
;;;		(negated by convention) to be proven, along with bindings and an axiom set.
;;;		Each theorem is then added to a list to prevent run-time errors from occuring. 
;;;		It prints each theorem and each axiom resolved with that theorem to produce a 
;;;		resolvent to be used as a new theorem. The function is recursive, and stops 
;;;		when success or failure is achieved. Success is defined as the theorem being
;;;		passed as nil, and failure is defined as passing in a theorem to the function
;;;		which has been seen by the fucntion before. Previous theorems are stored in a 
;;;		list "thms". Each time, computable predicates are evaluated if possible, and 
;;;		a theorem is resolved with the chosen axiom. The bindings are printed if the
;;;		original statement resolves to nil.      
;;;

(defun rtp (thm bind ax thms)
	(cond 
		((null thm) (print bind) 'SUCCESS)	 				;; success if nil theorem
		((find thm thms) 'FAILURE)							;; failure if repeated
		(t 
			(setq thms (cons thm thms))						;; add new theorem
			(format t "Theorem: ~S~%" thm)					;; print theorem
		  	(loop for i in ax  								;; for axiom is ax
		    	do (loop for j in (getliterals i) 			;; for literals in axiom
		        	do (loop for k in (getliterals thm) 	;; for literals in therom
		          		do (if  (multiple-value-bind (a b) 	;; return bindings
		          				(unify (negate j) k) a)  	
		          				(progn 
		          					(setq bind 				;; add bindings
		          						(append (multiple-value-bind (a b) 
		          					(unify (negate j) k) b) bind)) ;; unify
		          					(format t "Resolved with: ~S~%" ;; print axiom
		          						(instantiate i bind))
		          					(setf thm (resolve (compute 
		          						(instantiate thm bind)) 
		          					(instantiate i bind))))))))	;; instantiate
						(rtp thm bind ax thms))))				;; call recursively


;;;; TEST CASES 
;;; The following theorems can be proved in the Maximus domain. 
(rtp '(not (mortal Maximus)) nil Maxioms nil)
(rtp '(not (dead Maximus now)) nil Maxioms nil)

;;; The following theorem cannot be proved by resolution in the Maximus domain. 
(rtp '(erupted volcano 79) nil Maxioms nil)

;;; The following theorems can be proved in the Jack domain. 
(rtp '(kills Jack Puss) nil Jaxioms nil)
(rtp '(not (animal Puss)) nil Jaxioms nil)
;;; The following theorem cannot be proved by resolution in the Jack domain. 
(rtp '(not (kills Jack Puss)) nil Jaxioms nil)

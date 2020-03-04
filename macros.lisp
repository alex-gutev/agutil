;;;; macros.lisp
;;;;
;;;; Copyright 2018 Alexander Gutev
;;;;
;;;; Permission is hereby granted, free of charge, to any person
;;;; obtaining a copy of this software and associated documentation
;;;; files (the "Software"), to deal in the Software without
;;;; restriction, including without limitation the rights to use,
;;;; copy, modify, merge, publish, distribute, sublicense, and/or sell
;;;; copies of the Software, and to permit persons to whom the
;;;; Software is furnished to do so, subject to the following
;;;; conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be
;;;; included in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
;;;; OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;;; FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
;;;; OTHER DEALINGS IN THE SOFTWARE.

(in-package :agutil)


(defmacro! let-if ((&rest bindings) condition &body body)
  "Binds variables to different values computed by different
   init-forms based on whether CONDITION evaluates to true or
   false. BINDINGS is a list of bindings where the first element is
   the variable symbol the second element is the init-form to
   evaluated if CONDITION evaluates to true, the second element is the
   init-form to evaluate if CONDITION evaluates to false."

  (labels ((make-setf (sym value)
	     `(setf ,sym ,value))
	   (make-binding (binding sym)
	     `(,(first binding) ,sym)))

    (let ((gensyms (gensyms bindings :key #'car)))
      `(let ((,g!test ,condition) ,@gensyms)
	 (if ,g!test
	     (progn
	       ,@(mapcar #'make-setf gensyms (mapcar #'second bindings)))
	     (progn
	       ,@(mapcar #'make-setf gensyms (mapcar #'third bindings))))
	 (let
	     ,(mapcar #'make-binding bindings gensyms)
	   ,@body)))))

(defmacro! match-state (arg &body states)
  "Implements an FSM (Finite State Machine) where each state may
   specify a pattern (in the form accepted by the trivia pattern
   matcher) and a list of from states, when the argument matches the
   pattern of a particular state and the current state is in the
   state's from states list, the FSM transitions to that state.

   Each element in STATES is a list of the following form: (STATE
   PATTERN [:FROM STATES] . BODY) where STATE is a symbol identifying
   the state, PATTERN is the pattern to be matched, and STATES is the
   optional list of from states (it and the :FROM keyword may be
   excluded). if there is only one state it does not have to be in a
   list. If a state specifies no from states, it is as if all states,
   in the MATCH-STATE form, are specified as from states.

   When a state becomes the current state the forms in its BODY are
   executed, in which the machine may either transition to the next
   state using the lexically defined function (NEXT NEW-ARG) where
   NEW-ARG is the new argument to be matched against the patterns. If
   NEXT is never called in body the return value of the last form in
   BODY becomes the return value of the MATCH-STATE form.

   The initial argument is given by evaluating the form ARG. The
   initial state may be optionally specified, when the first element
   of STATES is :START the second element is taken as the form to be
   evaluated to produce the start state, otherwise the start state
   defaults to :START. Patterns are matched in the order given, the
   first state whose pattern matches (both the argument pattern and
   FROM list) becomes the current state."

  (let ((next (intern (string 'next)))
	(from-state (intern (string 'from-state))))
    (labels ((make-quote (thing)
	       `(quote ,thing))

	     (extract-from (body)
	       (match body
		 ((list* :from states body)
		  (values (cons 'or (mapcar #'make-quote (ensure-list states)))
			  body))

		 (_ (values '_ body))))

	     (make-clause (state)
	       (destructuring-bind (name pattern . body) state
		 (multiple-value-bind (from body) (extract-from body)
		   `(((guard ,from (not (and ,g!force (eq ,from-state ',name)))) ,pattern)
		     (flet ((,next (,g!arg &key force (from ',name))
			      (,g!next from force ,g!arg)))
		       (declare (ignorable (function,next)))
		       ,@body))))))

      (let-if ((start (second states) :start)
	       (body (cddr states) states))
	  (eq (first states) :start)

	`(labels ((,g!next (,from-state ,g!force ,g!arg)
		    (match* (,from-state ,g!arg)
		      ,@(mapcar #'make-clause body))))
	   (,g!next ,start nil ,arg))))))

(defmacro! nlet (name (&rest bindings) &body body)
  (let* ((vars (mapcar #'ensure-car bindings))
	 (syms (gensyms vars)))
    `(let ,bindings
       (block ,name
	 (tagbody
	    ,g!loop
	    (flet
		((,name ,syms
		   (setf ,@(mapcan #'list vars syms))
		   (go ,g!loop)))
	      (return-from ,name (progn ,@body))))))))

(defmacro! dohash ((key value hash &optional result) &body body)
  "Iterates over each element of HASH with the key bound to KEY and
   the value bound to VALUE. BODY is evaluated on each iteration in an
   implicit PROGN."

  (let ((key (or key g!key))
        (value (or value g!value)))
    `(with-hash-table-iterator (,g!next ,hash)
       (loop
          (multiple-value-bind (,g!next-p ,key ,value) (,g!next)
            (declare (ignorable ,key ,value))
            (unless ,g!next-p
              (return ,result))
            ,@body)))))


(defmacro update-let ((&rest bindings) &body body)
  "Establishes bindings to variables, which are visible to the forms
   in BODY, however each binding also has an update form, the result
   of which is assigned to the variable in the environment of the
   UPDATE-LET form itself.

   Each element of BINDINGS is a list of the form (VAR INIT-FORM
   UPDATE-FORM) where var is the variable symbol, INIT-FORM is the
   form of which the result is bound to VAR. This binding is visible
   to the forms in BODY. UPDATE-FORM is a form of which the result is
   assigned to VAR affecting the binding which is visible in the
   environment of the UPDATE-LET form itself, and not the binding
   which is visible in BODY. Each UPDATE-FORM is executed after the
   last form in BODY with the symbol OLD being bound to the value of
   the corresponding variable in the environment of the UPDATE-LET
   form.

   The value of the last form in BODY is returned."

  (multiple-value-bind (body declarations) (parse-body body)
    (let ((syms
           (loop
              for (var) in bindings
              for sym = (gensym (symbol-name var))
              collect (cons var sym))))

      `(let ,(loop for (var) in bindings
                for sym = (cdr (assoc var syms))
                collect (list sym var))
         (prog1
             (let ,(loop for (var init) in bindings
                      collect (list var init))
               ,@declarations
               (prog1 (progn ,@body)
                 ,@(loop
                      for (var nil update) in bindings
                      for sym = (cdr (assoc var syms))
                      collect
                        `(symbol-macrolet ((,(intern (symbol-name 'old)) ,sym))
                           (setf ,sym ,update)))))

           ,@(loop
                for (var) in bindings
                for sym = (cdr (assoc var syms))
                collect `(setf ,var ,sym)))))))

(defmacro with-struct-slots (conc-name (&rest slots) object &body body)
  "Same as WITH-SLOTS however for structures defined by
   DEFSTRUCT. CONC-NAME is the symbol, passed to the CONC-NAME option
   to DEFSTRUCT, which is prepended to each symbol in SLOTS to
   generate the name of the accessor function for the slot."

  (flet ((make-binding (slot)
           (ematch slot
             ((or (list var slot)
                  (and (type symbol) var slot))
              (list var (symb conc-name slot))))))

    `(with-accessors ,(mapcar #'make-binding slots) ,object
       ,@body)))

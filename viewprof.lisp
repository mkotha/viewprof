#!/usr/bin/sbcl --script

(require 'asdf)
(require 'cl-ncurses)

(defpackage viewprof
  (:use common-lisp)
  (:use cl-ncurses))

(in-package viewprof)

;;;; rose tree

(defstruct rtree
  value
  children) ; list of rtrees

(defun maptree (fn tree)
  (make-rtree
    :value (funcall fn (rtree-value tree))
    :children (mapcar (lambda (sub) (maptree fn sub))
                      (rtree-children tree))))

(defun tree-from-list (list)
  (destructuring-bind (val . children) list
    (make-rtree
      :value val
      :children (mapcar #'tree-from-list children))))

;;;; tree cursor

(defstruct cursor
  current
  parents) ; list of (node . index) conses, deepest first

(defun head-cursor (tree)
  (make-cursor
    :current tree
    :parents nil))

; returns the next visitable node in the tree, or nil
; if there is none
(defun cursor-next (cursor visitable)
  (cursor-next-upwards
    (cons (cons (cursor-current cursor) -1)
          (cursor-parents cursor))
    visitable))

(defun cursor-next-upwards (context visitable)
  (and context
    (destructuring-bind ((node . index) . rest) context
      (let* ((parents (mapcar #'car context))
             (next (position-if
                     (lambda (child)
                       (funcall visitable child parents))
                     (rtree-children node)
                     :start (1+ index))))
        (if next
          (make-cursor
            :current (elt (rtree-children node) next)
            :parents (cons (cons node next) rest))
          (cursor-next-upwards rest visitable))))))

(defun cursor-prev (cursor visitable)
  (let ((context (cursor-parents cursor)))
    (and context
       (destructuring-bind ((node . index) . rest) context
         (cursor-prev-downwards node index rest visitable)))))

(defun cursor-prev-downwards (node end context visitable)
   (let* ((parents (cons node (mapcar #'car context)))
          (prev (position-if
                  (lambda (child)
                    (funcall visitable child parents))
                  (rtree-children node)
                  :end end
                  :from-end t)))
     (if prev
       (cursor-prev-downwards
         (elt (rtree-children node) prev)
         nil
         (cons (cons node prev) context)
         visitable)
       (make-cursor
         :current node
         :parents context))))

(defun cursor-move (cursor count visitable)
  (loop while (< 0 count)
    do (decf count)
       (setf cursor (or (cursor-next cursor visitable) cursor)))
  (loop while (< count 0)
    do (incf count)
       (setf cursor (or (cursor-prev cursor visitable) cursor)))
  cursor)

;;;; .prof parser

(defun unindent (str)
  (let ((pos (or (position-if (lambda (x) (not (eql x #\ ))) str)
                  0)))
    (cons pos (subseq str pos))))

(defun get-unindented (bufstream)
  (if (cdr bufstream)
    (let ((putback (cdr bufstream)))
      (setf (cdr bufstream) nil)
      putback)
    (let ((line (read-line (car bufstream) nil)))
      (when line (unindent line)))))

(defun unget-unindented (bufstream value)
  (setf (cdr bufstream) value)
  nil)

(defun read-trees (input)
  (let ((buf (cons input nil)))
    (loop for tree = (read-subtree buf 0)
          while tree
          collect (car tree))))

(defun read-subtree (input minimum-level)
  (let ((head (get-unindented input)))
    (when head
      (destructuring-bind (head-level . head-str) head
        (if (< head-level minimum-level)
          (unget-unindented input head)
          (let* ((children (read-children input head-level))
                 (tree (make-rtree :value head-str :children children)))
            (cons tree head-level)))))))

(defun read-children (input parent-level)
  (let ((fst (read-subtree input (+ 1 parent-level))))
    (when fst
      (destructuring-bind (fst-subtree . level) fst
        (cons fst-subtree
          (loop for item = (read-subtree input level)
                while item 
                collect (car item)))))))

(defun read-trees-from-prof (input)
  (let ((cost-centre-count 0))
    (loop for line = (read-line input)
          do (when (search "COST CENTRE" line)
               (when (< 1 (incf cost-centre-count))
                 (read-line input); skip an empty line
                 (return (read-trees input)))))))

;;;; internal representation of an entire profile

(defstruct line
  name
  module
  idnum
  count
  individual
  inherited)

(defparameter *cost-centre-readtable* (copy-readtable nil))
(setf (readtable-case *cost-centre-readtable*) :preserve)
(set-syntax-from-char #\' #\a *cost-centre-readtable*)

(defun parse-line (line)
  (let* ((*read-eval* nil)
         (*readtable* *cost-centre-readtable*)
         (list-str (concatenate 'string "(" line ")"))
         (list (read-from-string list-str)))
    (destructuring-bind
        (name module idnum count idtime idalloc ihtime ihalloc) list
      (make-line
        :name name
        :module module
        :idnum idnum
        :count count
        :individual (cons idtime idalloc)
        :inherited (cons ihtime ihalloc)))))

(defun trees-from-file (file)
  (mapcar (lambda (tree) (maptree #'parse-line tree))
    (with-open-file (input file)
      (read-trees-from-prof input))))

; info on a cost center
(defstruct cc
  name
  module
  key
  occurrences)

; an occurrence in a call tree
(defstruct occurrence
  cc
  count
  parent ; occurrence
  children ; list of occurrences
  individual
  inherited)

; i store the whole information from a profiling report as a graph.
; a graph is represented by a hashtable from keys to ccs
; a key is a symbol of the form:
;   <name> <module>

; build a graph from a set of trees containing lines.
(defun build-graph (trees)
  (let ((table (make-hash-table)))
    (dolist (tree trees)
      (add-tree table tree))
    table))

(defun add-tree (table tree &optional parent)
  (let* ((root (rtree-value tree))
         (rootkey (key-from-line root))
         (cc (or (gethash rootkey table)
                 (setf (gethash rootkey table)
                   (make-cc
                     :name (line-name root)
                     :module (line-module root)
                     :key rootkey
                     :occurrences nil))))
         (occ (new-occurrence parent cc root)))
    (setf (cc-occurrences cc)
          (cons occ (cc-occurrences cc)))
    (dolist (child (rtree-children tree))
      (add-tree table child occ))))

(defun key-from-line (line)
  (make-key
    (line-name line)
    (line-module line)))

(defun make-key (name module)
  (intern (concatenate 'string
            (symbol-name name)
            " "
            (symbol-name module))))

(defun new-occurrence (parent cc line)
  (let ((occ (make-occurrence
               :cc cc
               :count (line-count line)
               :parent parent
               :children nil
               :individual (line-individual line)
               :inherited (line-inherited line))))
    (when parent
      (setf (occurrence-children parent)
            (cons occ (occurrence-children parent))))
    occ))

;;;; tree reversal

(defun parent-tree (root)
  (parent-tree-from
    (mapcar (lambda (occ)
              (cons occ
                (occurrence-inherited occ)))
            (cc-occurrences root))))

(defun parent-tree-from (heads)
  (make-rtree
    :value
      (cons (occurrence-cc (car (car heads)))
            (reduce #'add-timealloc
              (mapcar #'cdr heads)))
    :children
      (let* ((next-heads
               (remove-if (lambda (x) (not (car x)))
                 (mapcar (lambda (x)
                           (cons (occurrence-parent (car x))
                                 (cdr x)))
                   heads)))
             (g (group-on
                  (lambda (x) (occurrence-cc (car x)))
                  next-heads)))
        (mapcar #'parent-tree-from g))))

(defun add-timealloc (x y)
  (destructuring-bind ((a . b) (c . d)) (list x y)
    (cons (+ a c) (+ b d))))

(defun show-parent-tree-item (item)
  (destructuring-bind (cc . timealloc) item
    (format nil "(~A% ~A%) ~A ~A"
      (car timealloc)
      (cdr timealloc)
      (cc-name cc)
      (cc-module cc))))

;;;; curses interface

(defun init-curses ()
  (initscr)
  (start-color)
  (init-pair 1 COLOR_WHITE COLOR_BLACK)
  (init-pair 2 COLOR_BLACK COLOR_WHITE)
  (init-pair 3 COLOR_CYAN COLOR_BLACK)
  (noecho)
  (curs-set 0)
  (bkgd (color-pair 1))
  (clear)
  (move 0 0))

(defun render-tree-part (visitable height cursor cursor-pos)
  (let*
      ((endpoint (cursor-move cursor (- height cursor-pos 1) visitable))
       (startpoint (cursor-move endpoint (- 1 height) visitable)))
    (loop for c = startpoint then (cursor-next c visitable)
          for i from 1 to height
          while c
          collect (cursor-current c))))

(defun fix-cursor-pos (height requested-cursor-pos)
   (cond ((< height 5) 0)
         ((< requested-cursor-pos 2) 2)
         ((< (- height 3) requested-cursor-pos) (- height 3))
         (t requested-cursor-pos)))

(defun tree-view-filtering (view)
  (lambda (node context)
    (declare (ignore node))
    (or (not context)
        (gethash (car context) (tree-view-unfold-table view)))))

(defstruct tree-view
  heading
  ypos
  current
  unfold-table
  height
  width
  cursor-pos)

(defmacro with-color (w color-id &rest body)
  `(progn
     (wattron ,w (color-pair ,color-id))
     ,@body
     (wattroff ,w (color-pair ,color-id))))

(defun tree-view-render (w view)
  (let ((lines
          (render-tree-part
            (tree-view-filtering view)
            (1- (tree-view-height view))
            (tree-view-current view)
            (tree-view-cursor-pos view))))
    (wmove w 0 0)
    (werase w)
    (with-color w 3
      (wprintw w
        (fixed-width-line "" (tree-view-heading view) (tree-view-width view))))
    (dolist (node lines)
      (let ((line (format-tree-view-item
                    (rtree-value node)
                    (gethash node (tree-view-unfold-table view))
                    (consp (rtree-children node))
                    (tree-view-ypos view)
                    (tree-view-width view))))
        (if (eq node (cursor-current (tree-view-current view)))
          (with-color w 2 (wprintw w line))
          (wprintw w line))))))

(defstruct tree-view-item
  name
  module
  infostr
  indentation-level)

(defun format-tree-view-item
    (item unfolded has-children &optional (offset 0) (width 80))
  (let* ((idstr (format nil "~v,0T~A ~A         ~0,13T~A"
                        (tree-view-item-indentation-level item)
                        (cond ((not has-children) " ")
                              (unfolded "-")
                              (t "+"))
                        (tree-view-item-name item)
                        (tree-view-item-module item)))
         (head (subseq idstr (min offset (length idstr))))
         (info (tree-view-item-infostr item)))
    (fixed-width-line head info width)))

(defun fixed-width-line (x y width)
  (let* ((x-length (length x))
         (x-width (- width 1 (length y))))
    (if (<= x-length x-width)
      (format nil "~A~v,0T ~A~%" x x-width y)
      (format nil "~A... ~A~%" (subseq x 0 (- x-width 3)) y))))

(defun make-tree-view-tree (item-maker tree &optional (level 0))
  (make-rtree
    :value (funcall item-maker level (rtree-value tree))
    :children (mapcar
                (lambda (child) (make-tree-view-tree item-maker child (1+ level)))
                (rtree-children tree))))

(defun tree-view-item-from-line (level line)
  (make-tree-view-item
    :name (line-name line)
    :module (line-module line)
    :infostr (format nil "~A  ~6,2F ~6,2F  ~6,2F ~6,2F"
                     (line-count line)
                     (car (line-individual line))
                     (cdr (line-individual line))
                     (car (line-inherited line))
                     (cdr (line-inherited line)))
    :indentation-level level))

(defun tree-view-item-from-parent-tree-item (level pitem)
  (destructuring-bind (cc . (time . alloc)) pitem
    (let ((total-inher (cc-sum #'add-timealloc #'occurrence-inherited cc))
          (total-indiv (cc-sum #'add-timealloc #'occurrence-individual cc)))
    (make-tree-view-item
      :name (cc-name cc)
      :module (cc-module cc)
      :infostr (format nil "~A ~6,2F ~6,2F  ~6,2F ~6,2F  ~6,2F ~6,2F"
                       (cc-sum #'+ #'occurrence-count cc)
                       time
                       alloc
                       (car total-indiv)
                       (cdr total-indiv)
                       (car total-inher)
                       (cdr total-inher))
      :indentation-level level))))

(defun cc-sum (reducer mapper cc)
  (reduce reducer (mapcar mapper (cc-occurrences cc))))

(defun tree-view (tree heading height width)
  (make-tree-view
    :heading heading
    :ypos 0
    :current (head-cursor tree)
    :unfold-table (make-hash-table)
    :height height
    :width width
    :cursor-pos 0))

(defun ui-loop (tree window width height)
  (let* ((base-view (tree-view
                      (make-tree-view-tree #'tree-view-item-from-line tree)
                      "count     individual      inherited"
                      height
                      width))
         (view base-view)
         (graph (build-graph (list tree))))
    (flet ((reverse-tree-view ()
             (let ((cc (gethash (tree-view-current-key view) graph)))
               (when cc
                 (tree-view
                   (make-tree-view-tree
                     #'tree-view-item-from-parent-tree-item
                     (parent-tree cc))
                   "count  contribution     individual      inherited"
                   height
                   width)))))
      (loop do
        (tree-view-render window view)
        (let ((ch (getch)))
          (cond
            ((= ch (char-code #\j)) (tree-view-dn view))
            ((= ch (char-code #\k)) (tree-view-up view))
            ((= ch (ctrl-code #\D)) (tree-view-dn-halfwindow view))
            ((= ch (ctrl-code #\U)) (tree-view-up-halfwindow view))
            ((= ch (char-code #\l)) (tree-view-right view))
            ((= ch (char-code #\h)) (tree-view-left view))
            ((= ch (char-code #\ )) (tree-view-toggle view))
            ((= ch (char-code #\r))
              (setf view
                (if (eq view base-view)
                  (or (reverse-tree-view) view)
                  base-view)))
            ((= ch (char-code #\q)) (return)))))
      nil)))

(defun ctrl-code (char)
  (logandc1 64 (char-code char)))

(defun ui-main (tree)
  (init-curses)
  (ui-loop
    tree
    *stdscr*
    (min 120 (1- *cols*))
    *lines*)
  (endwin))

(defun tree-view-set-cursor-pos (view pos)
  (setf (tree-view-cursor-pos view)
        (fix-cursor-pos (tree-view-height view) pos)))

(defun tree-view-up (view)
  (let ((p (cursor-prev (tree-view-current view) (tree-view-filtering view))))
    (when p
      (setf (tree-view-current view) p)
      (tree-view-set-cursor-pos view (1- (tree-view-cursor-pos view))))))

(defun tree-view-dn (view)
  (let ((p (cursor-next (tree-view-current view) (tree-view-filtering view))))
    (when p
      (setf (tree-view-current view) p)
      (tree-view-set-cursor-pos view (1+ (tree-view-cursor-pos view))))))

(defun tree-view-up-halfwindow (view)
  (tree-view-move-halfwindow #'tree-view-up view))

(defun tree-view-dn-halfwindow (view)
  (tree-view-move-halfwindow #'tree-view-dn view))

(defun tree-view-move-halfwindow (mv view)
  (dotimes (k (floor (/ (tree-view-height view) 2)))
    (funcall mv view)))

(defun tree-view-right (view)
  (setf (tree-view-ypos view)
        (+ 2 (tree-view-ypos view))))

(defun tree-view-left (view)
  (setf (tree-view-ypos view)
        (max 0
             (- (tree-view-ypos view) 2))))

(defun tree-view-toggle (view)
  (tree-view-toggle-unfold
    view
    (cursor-current (tree-view-current view))))

(defun tree-view-toggle-unfold (view node)
  (setf (gethash node (tree-view-unfold-table view))
        (not (gethash node (tree-view-unfold-table view)))))

(defun tree-view-current-key (view)
  (let ((item (rtree-value (cursor-current (tree-view-current view)))))
    (make-key
      (tree-view-item-name item)
      (tree-view-item-module item))))

;;;; utilities

(defun group-on (make-key list)
  (let ((table (make-hash-table)))
    (dolist (item list)
      (let ((key (funcall make-key item)))
        (setf (gethash key table)
              (cons item (gethash key table)))))
    (loop for x being the hash-values in table
          collect x)))

;;;; driver

(defun main (args)
  (if (= (length args) 1)
    (let ((trees (trees-from-file (car args))))
      (if trees
        (ui-main (car trees))
        (format t "viewprof: Failed to read ~A" (car args))))
    (format t "Usage: viewprof.lisp PROG.prof")))

(main (cdr sb-ext:*posix-argv*))

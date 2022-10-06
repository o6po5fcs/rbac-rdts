#lang racket

(provide logical-and logical-or key-matches?)

(define (logical-and . args)
  (if (null? args)
      #f
      (and (car args) (apply logical-and (cdr args)))))

(define (logical-or . args)
  (if (null? args)
      #t
      (or (car args) (apply logical-or (cdr args)))))

(define (key-matches? user-id stored-key provided-key)
  (let ((stored-sp (string-split stored-key "-"))
        (provided-sp (string-split provided-key "-")))
    (cond ((not (eq? 2 (length stored-sp)))
           #f)
          ((not (eq? 2 (length provided-sp)))
           #f)
          ((not (equal? (car stored-sp) "stored"))
           #f)
          ((not (equal? (car provided-sp) "provided"))
           #f)
          ((not (equal? (cadr stored-sp) user-id))
           #f)
          ((not (equal? (cadr provided-sp) user-id))
           #f)
          (else #t))))

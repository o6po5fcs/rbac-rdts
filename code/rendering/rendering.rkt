#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;                                                            ;;;
;;; Rendering                                                  ;;;
;;;                                                            ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; This file can be used to typeset the formalism.            ;;;
;;;                                                            ;;;
;;; Note that Redex uses the pict library, which instantiates  ;;;
;;; a graphics context (even when pict is only used to render  ;;;
;;; to files). An unfortunate side-effect is that this library ;;;
;;; tends to fail (e.g., citing GTk errors) when run headless. ;;;
;;; Using a Virtual X Server Framebuffer such as VXFB should   ;;;
;;; remedy this problem.                                       ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require redex
         redex/pict
         "../formalisation/CommonLang.rkt"
         "../formalisation/LeaderLang.rkt"
         "../formalisation/ReplicaLang.rkt"
         racket/draw)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Ensures that our global default render config is in effect. ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (reset-render-style!)  
  ; https://docs.racket-lang.org/pict/Basic_Pict_Constructors.html#%28def._%28%28lib._pict%2Fmain..rkt%29._text%29%29
  ; The style argument must be one of the following:
  ;   null — the default, same as 'default
  ;   a font% object
  ;   a font family symbol, such a 'roman (see font%)
  ;   a font face string, such as "Helvetica" (see font%)
  ;   (cons str sym) combining a face string and a font family (in case the face is unavailable; see font%)
  ;   (cons 'bold style) for a valid style
  ;   (cons 'italic style)
  ;   (cons 'subscript style)
  ;   (cons 'superscript style)
  ;   (cons 'large-script style) — makes subscripts and superscripts larger, which is more suitable for small text sizes as might appear in print
  ;   (cons 'caps style)
  ;   (cons 'combine style) — allows kerning and ligatures (the default, unless the 'modern family is specified)
  ;   (cons 'no-combine style) — renders characters individually
  ;   (cons 'aligned style) — enables hinting, which rounds metrics to integers
  ;   (cons 'unaligned style) — disables hinting (which is the default), so that metrics are scalable
  ;   (cons color style) — where color is a color% object, colorizes the text
  ; If both 'combine and 'no-combine are specified, the first one in style takes precedence.
  ; Similarly, if both 'aligned and 'unaligned are specified, the first one in style takes precedence.
  ; If 'caps is specified, the angle must be zero.

  ;(define sans-serif-style 'swiss)
  (define juliamono (make-font #:size 10.5
                                #:face "JuliaMono"
                                ))
  (define sans-serif-style juliamono)

  ; (define roman-style 'roman)
  (define roman-style "Linux Libertine")
  
  
  ; The label-style parameter is used for reduction-rule labels.
  ; Default is 'swiss which is "Arial" on Windows, and "Helvetica" on other platforms.
  (label-style sans-serif-style)

  ; The literal-style parameter is used for names that aren’t non-terminals that appear in patterns.
  ; Default is 'swiss which is "Arial" on Windows, and "Helvetica" on other platforms.
  (literal-style sans-serif-style)

  ; The metafunction-style parameter is used for the names of metafunctions.
  ; Default is 'swiss which is "Arial" on Windows, and "Helvetica" on other platforms.
  (metafunction-style sans-serif-style)

  ; The paren-style parameter is used for parentheses (including “[”, “]”, “{”, and “}”,
  ; as well as “(” and “)”) and for keywords, but it is not used for the square brackets of in-hole decompositions
  ; Use paren-style for keywords.
  ; Default is 'roman which is "Times New Roman" on Windows, and "Serif" on other platforms.
  (paren-style roman-style)

  ; [paren-style] is not used for the square brackets of in-hole decompositions, which use the default-style parameter
  ; The default-style parameter is used for parenthesis, the dot in dotted lists, spaces, the “where” and “fresh” in side-conditions,
  ; and other places where the other parameters aren’t used.
  ; Default is 'roman which is "Times New Roman" on Windows, and "Serif" on other platforms.
  (default-style roman-style)

  ; The grammar-style parameter is used for the “::=” and “|” in grammars.
  ; Default is 'roman which is "Times New Roman" on Windows, and "Serif" on other platforms.
  (grammar-style roman-style)


  ;Two parameters style the text in the (optional) “underscore” component of a non-terminal reference.
  ; The first, non-terminal-subscript-style, applies to the segment between the underscore and the first caret (^) to follow it;
  ; the second, non-terminal-superscript-style, applies to the segment following that caret.
  ; For example, in the non-terminal reference x_y^z, x has style non-terminal-style, y has style non-terminal-subscript-style,
  ; and z has style non-terminal-superscript-style.
  ; The only exception to this is when the subscript section consists only of unicode prime characters (′),
  ; in which case the non-terminal-style is used instead of the non-terminal-subscript-style.

  ; the default is '(subscript italic . roman)
  (non-terminal-subscript-style `(subscript large-script italic . ,roman-style))
  ; the default is '(superscript italic . roman)
  (non-terminal-superscript-style `(superscript large-script italic . ,roman-style))
  ; the default is '(italic . roman)
  (non-terminal-style `(italic . ,roman-style))


  
  ; This parameter controls the amount of extra horizontal space around the reduction relation arrow.
  ; Defaults to 0.
  (arrow-space 0)

  ; This parameter controls the amount of extra space before the label on each rule,
  ; except in the 'vertical and 'vertical-overlapping-side-conditions modes, where it has no effect.
  ; Defaults to 0.
  (label-space 0)

  
  (label-font-size 13)         ; default is 14
  (metafunction-font-size 13)  ; default is 14
  (default-font-size 13)       ; default is 14

  ; Controls the amount of space between rule in a reduction relation.
  ; Horizontal and compact-vertical renderings add this parameter’s amount to (reduction-relation-rule-extra-separation) to compute the full separation.
  ; default is 4
  (reduction-relation-rule-separation 4) 
  ; Controls the amount of space between rule in a reduction relation for a horizontal or compact-vertical rendering,
  ; in addition to (reduction-relation-rule-separation).
  ; default is 4
  (reduction-relation-rule-extra-separation 4)

  ; Controls the amount of space between lines within a reduction-relation rule.
  ; Default is 2.
  (reduction-relation-rule-line-separation 2)

  ; Controls if the open and close quotes for strings are turned into “ and ” or are left as merely ".
  ; default is #t
  (curly-quotes-for-strings #t)


  ; Controls the amount of space around the horizontal bar when rendering a relation (that was created by define-relation).
  ; Default is 4.
  (horizontal-bar-spacing 4)

  ; Controls the amount of vertical space between different metafunctions rendered together with render-metafunctions.
  (metafunction-gap-space 2)

  ; Controls the amount of vertical space between different rules within a metafunction as rendered with render-metafunction or render-metafunctions.
  (metafunction-rule-gap-space 2)

  ; Controls the amount of vertical space between different lines within a metafunction rule as rendered with render-metafunction or render-metafunctions.
  (metafunction-line-gap-space 2)

  ; Determines a width that is used for putting metafunction side conditions on a single line when using a style like
  ; 'left-right/compact-side-conditions (as the value of metafunction-pict-style).
  ; The default value is 0, which means that side conditions are joined on a line only when joining them
  ; does not change the overall width of the rendered metafunction.
  ; A larger value allows side conditions to be joined when they would make the rendered form wider,
  ; as long as the overall width of the metafunction does not exceed the specified value.
  (metafunction-fill-acceptable-width 0)


  ; This parameter controls the style used by default for the reduction relation.
  ; It can be 'horizontal, where the left and right-hand sides of the reduction rule are beside each other
  ; or 'vertical, where the left and right-hand sides of the reduction rule are above each other.
  ; The 'compact-vertical style moves the reduction arrow to the second line and uses less space between lines.
  ; The 'vertical-overlapping-side-conditions variant, the side-conditions don’t contribute to the width of the pict,
  ; but are just overlaid on the second line of each rule.
  ; The 'horizontal-left-align style is like the 'horizontal style, but the left-hand sides of the rules are
  ; aligned on the left, instead of on the right. The 'horizontal-side-conditions-same-line is like 'horizontal,
  ; except that side-conditions are on the same lines as the rule, instead of on their own line below.
  (rule-pict-style 'horizontal)

  ; https://docs.racket-lang.org/redex/reference.html#%28def._%28%28lib._redex%2Fpict..rkt%29._metafunction-pict-style%29%29
  (metafunction-pict-style 'up-down/vertical-side-conditions)
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; What follows is rather straightforward: for all images in the main paper, ;;
;; we provide a typesetting routine which formats things the way we want.    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (render-commonlang (filepath #f))
  (reset-render-style!)
  (non-terminal-gap-space -1.5)
  (render-language
   CommonLang
   filepath
   #:nts (remove* '(other-reserved-symbols) (language-nts CommonLang))))


(define (render-replicalang (filepath #f))
  (reset-render-style!)
  (non-terminal-gap-space -1.5)
  (render-language ReplicaLang filepath))


(define (render-leaderlang (filepath #f))
  (reset-render-style!)
  (non-terminal-gap-space -1.5)
  (render-language LeaderLang filepath))


(define (render-is-readable (filepath #f))
  (reset-render-style!)
  (with-compound-rewriter
      'element-of
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ∈ " rhs ""))
    (with-compound-rewriter
        'list-without
      (λ (lws)
        (define lhs (list-ref lws 2))
        (define rhs (list-ref lws 3))
        (list "" lhs "\\" rhs ""))
      (if filepath
          (render-judgment-form is-readable filepath)
          (render-judgment-form is-readable)))))


(define (render-matches-in-env (filepath #f))
  (reset-render-style!)
  (with-compound-rewriter
      'element-of
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ∈ " rhs ""))
    (with-compound-rewriter
        'list-without
      (λ (lws)
        (define lhs (list-ref lws 2))
        (define rhs (list-ref lws 3))
        (list "" lhs "\\" rhs ""))
      (if filepath
          (render-judgment-form matches-in-env filepath)
          (render-judgment-form matches-in-env)))))


(define (render-red-replica (filepath #f))
  (reset-render-style!)
  (reduction-relation-rule-separation 0)
  (reduction-relation-rule-extra-separation 0)
  (reduction-relation-rule-line-separation 0)
  (with-compound-rewriter
      'list-without
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs "\\" rhs ""))
    (with-compound-rewriter
        'element-of
      (λ (lws)
        (define lhs (list-ref lws 2))
        (define rhs (list-ref lws 3))
        (list "" lhs " ∈ " rhs ""))
      (with-compound-rewriter
          'distinct
        (λ (lws)
          (define lhs (list-ref lws 2))
          (define rhs (list-ref lws 3))
          (list "" lhs " ≠ " rhs ""))
        (if filepath
            (render-reduction-relation red-replica filepath)
            (render-reduction-relation red-replica))))))


(define (render-handle-request (filepath #f))
  (reset-render-style!)
  (metafunction-pict-style 'left-right/vertical-side-conditions)
  (metafunction-gap-space 0)
  (metafunction-line-gap-space 0)
  (metafunction-rule-gap-space 0)
  
  (with-compound-rewriter
      'element-of
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ∈ " rhs ""))
    (with-compound-rewriter
        'list-without
      (λ (lws)
        (define lhs (list-ref lws 2))
        (define rhs (list-ref lws 3))
        (list "" lhs "\\" rhs ""))
      (if filepath
          (render-metafunction handle-request filepath)
          (render-metafunction handle-request)))))


(define (render-excerpt-for-role (filepath #f))
  (reset-render-style!)
  (metafunction-pict-style 'left-right/vertical-side-conditions)
  (metafunction-up/down-indent 0)
  (metafunction-rule-gap-space 5)
  (with-compound-rewriter
      'distinct
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ≠ " rhs ""))
    (if filepath
        (render-metafunction excerpt-for-role filepath)
        (render-metafunction excerpt-for-role))))


(define (render-readable-projection (filepath #f))
  (reset-render-style!)
  (metafunction-up/down-indent 0)
  (metafunction-rule-gap-space 0)
  (metafunction-gap-space 0)
  (metafunction-line-gap-space 0)
  (with-compound-rewriter
      'distinct
    (λ (lws)
      (define lhs (list-ref lws 2))
      (define rhs (list-ref lws 3))
      (list "" lhs " ≠ " rhs ""))
    (if filepath
        (render-metafunction readable-projection filepath)
        (render-metafunction readable-projection))))




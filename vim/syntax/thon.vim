" Vim syntax file
" Language: Thon
" Maintainer: Evan
" Latest Revision: 2026-03-03

if exists("b:current_syntax")
  finish
endif

" Keywords - expression forms
syn keyword thonKeyword FN DECLARE IS IN END GENERIC
syn keyword thonKeyword FIX CASE OF WHEN
syn keyword thonKeyword PACKAGE AS OPEN
syn keyword thonKeyword DATA IF THEN ELSE
syn keyword thonKeyword IFZ FUN

" Built-in operations
syn keyword thonBuiltin SUCC FOLD UNFOLD
syn keyword thonBuiltin LEFT RIGHT
syn keyword thonBuiltin FST SND

" Constants
syn keyword thonConstant ZERO UNIT

" Type keywords
syn keyword thonType NAT FORALL SOME REC

" Comments (ML-style, nested)
syn region thonComment matchgroup=thonComment start="(\*" end="\*)" contains=thonComment,thonTodo
syn keyword thonTodo TODO FIXME XXX NOTE contained

" Numbers (for numeric literals if any)
syn match thonNumber "\<\d\+\>"

" Operators
syn match thonOperator "->"
syn match thonOperator "\*\ze[^)]\|$"
syn match thonOperator "|"
syn match thonOperator "\."
syn match thonOperator "=>"
syn match thonOperator ":"
syn match thonOperator "="

" Delimiters
syn match thonDelimiter "[\[\]{}]"
syn match thonDelimiter "(\ze[^*]"
syn match thonDelimiter ")"
syn match thonDelimiter ","

" Identifiers (lowercase starting)
syn match thonIdentifier "\<[a-z_][a-zA-Z0-9_']*\>"

" Type variables (lowercase after FORALL/SOME/REC binding)
syn match thonTypeVar "\<[a-z][a-zA-Z0-9_']*\>" contained

" Highlight links
hi def link thonKeyword Keyword
hi def link thonBuiltin Function
hi def link thonConstant Constant
hi def link thonType Type
hi def link thonComment Comment
hi def link thonTodo Todo
hi def link thonNumber Number
hi def link thonOperator Operator
hi def link thonDelimiter Delimiter
hi def link thonIdentifier Identifier

let b:current_syntax = "thon"

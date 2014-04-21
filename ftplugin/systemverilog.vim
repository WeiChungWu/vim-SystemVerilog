" Vim filetype plugin file
" Language:	SystemVerilog
" Maintainer:	WeiChung Wu <exelion04 at gmail dot com>
" Last Change:	Thu Jan 13 13:05:54 CST 2011

" Only do this when not done yet for this buffer
if exists("b:did_ftplugin")
  finish
endif

" Don't load another plugin for this buffer
let b:did_ftplugin = 1

" Undo the plugin effect
let b:undo_ftplugin = "setlocal fo< com< tw<"
    \ . "| unlet! b:browsefilter b:match_ignorecase b:match_words"

" Set 'formatoptions' to break comment lines but not other lines,
" and insert the comment leader when hitting <CR> or using "o".
setlocal fo-=t fo+=croqlm1

" Set 'comments' to format dashed lists in comments.
setlocal comments=sO:*\ -,mO:*\ \ ,exO:*/,s1:/*,mb:*,ex:*/,://

" Format comments to be up to 78 characters long
"if &textwidth == 0 
"  setlocal tw=78
"endif

set cpo-=C

" Win32 can filter files in the browse dialog
"if has("gui_win32") && !exists("b:browsefilter")
"  let b:browsefilter = "Verilog Source Files (*.v)\t*.v\n" .
"	\ "All Files (*.*)\t*.*\n"
"endif

" Let the matchit plugin know what items can be matched.
if exists("loaded_matchit")
  let b:match_ignorecase=0
  let b:match_words=
    \ '\<begin\>:\<end\>,' .
    \ '\<if\>:\<else\>,' .
    \ '`if\%[n]def\>:`else\>:`endif\>,' .
    \ '\<case\%[xz]\>\|\<randcase\>:\<endcase\>,' .
    \ '\%(disable\s\+\)\@<!\<fork\>:\<\%(join\|join_any\|join_none\)\>,' .
    \ '\<module\>:\<endmodule\>,' .
    \ '\<function\>:\<return\>:\<endfunction\>,' .
    \ '\<task\>:\<endtask\>,' .
    \ '\<program\>:\<endprogram\>,' .
    \ '\<package\>:\<endpackage\>,' .
    \ '\<class\>:\<endclass\>,' .
    \ '\<covergroup\>:\<endgroup\>,' .
    \ '\<packet\>:\<endpacket\>,' .
    \ '\<interface\>:\<endinterface\>,' .
    \ '\<clocking\>:\<endclocking\>,' .
    \ '\<randsequence\>:\<endsequence\>,' .
    \ '\<specify\>:\<endspecify\>,' .
    \ '`uvm_object\%(_param\)\=_utils_begin\>:`uvm_object_utils_end\>,' .
    \ '`uvm_component\%(_param\)\=_utils_begin\>:`uvm_component_utils_end\>'
endif

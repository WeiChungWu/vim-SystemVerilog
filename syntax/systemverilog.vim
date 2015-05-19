" Vim syntax file
" Language:	SystemVerilog
" Maintainer:	WeiChung Wu <exelion04 at gmail dot com>
" Last Change:	2011 Aug 04
"
" Credits:
"   Originally created by
"       Dave Eggum (opine at bluebottle dOt com)

" NOTE: extra white space at the end of the line will be highlighted if you
" add this line to your colorscheme:

" highlight SpaceError    guibg=#204050

" (change the value for guibg to any color you like)

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

" A bunch of useful SV keywords
syn keyword	svStatement	always always_comb always_ff always_latch assert
syn keyword	svStatement	break return continue fork join disable force release assign
syn keyword	svStatement	join_any join_none frokjoin binsof intersect wait wait_order

syn keyword	svLabel		bind constraint covergroup coverpoint
syn keyword	svLabel		class CLOCK clocking default function generate interface modport 
syn keyword	svLabel		package program property randseq sequence specify
syn keyword	svLabel		task 
syn keyword	svLabel		begin initial module forever import 
syn keyword	svLabel		end endclass endfunction endgenerate endtask endprogram endmodule 
syn keyword	svLabel		endinterface endpackage endproperty endclocking endgroup

syn keyword	svConditional	if iff else case casex casez endcase randcase
syn keyword	svConditional	unique priority randsequence endsequence 
syn keyword 	svRepeat	repeat while for do foreach
syn keyword 	svModifier	after all any around assoc_size async
syn keyword 	svModifier	before big_endian bit_normal bit_reverse export
syn keyword 	svModifier	extends extern little_endian local hdl_node hdl_task
syn keyword 	svModifier	negedge none packed protected posedge public rules
syn keyword 	svModifier	shadow soft solve static super this typedef unpacked var
syn keyword 	svModifier	vca virtual virtuals wildcard with
syn keyword 	svModifier	ref const pure automatic

syn keyword 	svType		reg string enum event bit semaphore
syn keyword 	svType		rand randc integer parameter
syn keyword 	svType		logic int mailbox input output inout unsigned time wire

"syn keyword     svDeprecated	call_func call_task close_conn get_bind get_bind_id
"syn keyword     svDeprecated	get_conn_err mailbox_receive mailbox_send make_client
"syn keyword     svDeprecated	make_server simwave_plot up_connections

" predefined tasks and functions
"syn keyword 	svTask		alloc assoc_index cast_assign cm_coverage
"syn keyword 	svTask		cm_get_coverage cm_get_limit delay error error_mode
"syn keyword 	svTask		exit fclose feof ferror fflush flag fopen fprintf
"syn keyword 	svTask		freadb freadh freadstr get_cycle get_env get_memsize
"syn keyword 	svTask		get_plus_arg getstate get_systime get_time get_time_unit
"syn keyword 	svTask		initstate lock_file mailbox_get mailbox_put os_command
"syn keyword 	svTask		printf prodget prodset psprintf query query_str query_x
"syn keyword 	svTask		rand48 random region_enter region_exit rewind
"syn keyword 	svTask		semaphore_get semaphore_put setstate signal_connect
"syn keyword 	svTask		sprintf srandom sscanf stop suspend_thread sync
"syn keyword 	svTask		trace trigger unit_delay unlock_file urand48
"syn keyword 	svTask		urandom urandom_range 
"syn keyword 	svTask		vsv_call_func vsv_call_task vsv_get_conn_err
"syn keyword 	svTask		vsv_make_client vsv_make_server vsv_up_connections
"syn keyword 	svTask		vsv_wait_for_done vsv_wait_for_input wait_child wait_var
"  " ChungWu modify
"syn keyword 	svTask		wait cast display displayb displayh write
syn match       svTask          "\$[a-zA-Z0-9_]\+\>"

syn cluster	svOperGroup	contains=svOperator,svOperParen,svNumber,svString,svOperOk,svType
" syn match	svOperator	"++\|--\|&\|\~&\||\|\~|\|^\|\~^\|\~\|><"
" syn match	svOperator	"*\|/\|%\|+\|-\|<<\|>>\|<\|<=\|>\|>=\|!in"
" syn match	svOperator	"=?=\|!?=\|==\|!=\|===\|!==\|&\~\|^\~\||\~"
" syn match	svOperator	"&&\|||\|=\|+=\|-=\|*=\|/=\|%=\|<<=\|>>=\|&="
" syn match	svOperator	"|=\|^=\|\~&=\|\~|=\|\~^="

syn match	svOperator	"[&|\~><!*@+/=,.\^\-]"
syn keyword	svOperator	or inside dist not

" sv class methods
syn keyword	svMethods	atobin atohex atoi atooct backref bittostr capacity
syn keyword	svMethods	compare Configure constraint_mode DisableTrigger
syn keyword	svMethods	DoAction empty EnableCount EnableTrigger Event find
syn keyword	svMethods	find_index find_first find_first_index find_last find_last_index
syn keyword	svMethods	GetAssert get_at_least get_auto_bin getc GetCount get_coverage_goal get_cov_weight
syn keyword	svMethods	get_cross_bin_max GetFirstAssert GetName GetNextAssert
syn keyword	svMethods	get_status get_status_msg hide hash icompare insert
syn keyword	svMethods	inst_get_at_least inst_get_auto_bin_max inst_get_collect
syn keyword	svMethods	inst_get_coverage_goal inst_get_cov_weight inst_getcross_bin_max
syn keyword	svMethods	inst_query inst_set_at_least inst_set_auto_bin_max
syn keyword	svMethods	inst_set_bin_activiation inst_set_collect inst_set_coverage_goal
syn keyword	svMethods	inst_set_cov_weight inst_set_cross_bin_max itoa last_index
syn keyword	svMethods	len load match max max_index min min_index new object_compare
syn keyword	svMethods	object_compare object_copy object_print pack pick_index
syn keyword	svMethods	pop_back pop_front post_boundary postmatch post_pack post_pack
syn keyword	svMethods	post_randomize post_randomize post_unpack post_unpack
syn keyword	svMethods	pre_boundary prematch pre_pack pre_pack pre_randomize
syn keyword	svMethods	pre-randomize pre_unpack product push_back push_front putc query
syn keyword	svMethods	query_str rand_mode randomize reserve reverse rsort search
syn keyword	svMethods	set_at_least set_auto_bin_max set_bin_activiation
syn keyword	svMethods	set_coverage_goal set_cov_weight set_cross_bin_max 
syn keyword	svMethods	shuffle size sort substr sum thismatch tolower toupper unique_index
syn keyword	svMethods	Wait
syn keyword	svMethods	num delete exists first last next prev

" interface keywords
"syn keyword	svInterface	ASYNC CLOCK gnr gr0 gr1 grx grz NHOLD nr NR0 NR1
"syn keyword	svInterface	NRZ NRZ NSAMPLE PHOLD PR0 PR1 PRX PRZ r0 r1 rx snr
"syn keyword	svInterface	sr0 sr1 srx srz depth inout input output
"syn match      svInterface	"\$\w\+"


syn keyword	svTodo		contained TODO FIXME XXX FINISH

" svCommentGroup allows adding matches for special things in comments
syn cluster	svCommentGroup	contains=svTodo

" String and Character constants
" Highlight special characters (those which have a backslash) differently
syn match	svSpecial	display contained "\\\(x\x\+\|\o\{1,3}\|.\|$\)"
syn match	svFormat	display "%\(\d\+\$\)\=[-+' #0*]*\(\d*\|\*\|\*\d\+\$\)\(\.\(\d*\|\*\|\*\d\+\$\)\)\=\([hlL]\|ll\)\=\([bdhiuoxXDOUfeEgGcCsSpnmt]\|\[\^\=.[^]]*\]\)" contained
syn match	svFormat	display "%%" contained
syn region	svString	start=+"+ skip=+\\\\\|\\"+ end=+"+ contains=svSpecial,svFormat,@Spell
syn region	svConcat	contained transparent oneline start='{' end='}'

" svCppString: same as svString, but ends at end of line
syn region	svCppString	start=+"+ skip=+\\\\\|\\"\|\\$+ excludenl end=+"+ end='$' contains=svSpecial,svFormat,@Spell

syn match	svCharacter		"'[^\\]'"
syn match	svCharacter		"L'[^']*'" contains=svSpecial
syn match	svSpecialError		"'\\[^'\"?\\abefnrtv]'"
syn match	svSpecialCharacter	"'\\['\"?\\abefnrtv]'"
syn match	svSpecialCharacter	display	"'\\\o\{1,3}'"
syn match	svSpecialCharacter	display	"'\\x\x\{1,2}'"
syn match	svSpecialCharacter	display	"L'\\x\x\+'"

" highlight trailing white space
syn match	svSpaceError		display	excludenl "\s\+$"
syn match	svSpaceError		display	" \+\t"me=e-1

"catch errors caused by wrong parenthesis and brackets
syn cluster	svParenGroup		contains=svParenError,svIncluded,svSpecial,svCommentSkip,svCommentString,svComment2String,@svCommentGroup,svCommentStartError,svUserCont,svUserLabel,svBitField,svCommentSkip,svOctalZero,svCppOut,svCppOut2,svCppSkip,svFormat,svNumber,svFloat,svOctal,svOctalError,svNumbersCom

syn region	svParen		transparent start='(' end=')' contains=ALLBUT,@svParenGroup,svCppParen,svErrInBracket,svCppBracket,svCppString,@Spell
" svCppParen: same as svParen but ends at end-of-line; used in svDefine
syn region	svCppParen	transparent start='(' skip='\\$' excludenl end=')' end='$' contained contains=ALLBUT,@svParenGroup,svErrInBracket,svParen,svBracket,svString,@Spell
syn match	svParenError	display "[\])]"
" syn match	svErrInParen	display contained "[\]{}]"
syn match	svErrInParen	display contained "[\]]"
syn region	svBracket	transparent start='\[' end=']' contains=ALLBUT,@svParenGroup,svErrInParen,svCppParen,svCppBracket,svCppString,@Spell

" svCppBracket: same as svParen but ends at end-of-line; used in svDefine
syn region	svCppBracket	transparent start='\[' skip='\\$' excludenl end=']' end='$' contained contains=ALLBUT,@svParenGroup,svErrInParen,svParen,svBracket,svString,@Spell
syn match	svErrInBracket	display contained "[);{}]"

"integer number, or floating point number without a dot and with "f".
syn case ignore
syn match	svNumbers	display transparent "\<\d\|\.\d" contains=svNumber,svFloat,svOctalError,svOctal
" Same, but without octal error (for comments)
syn match	svNumbersCom	display contained transparent "\<\d\|\.\d" contains=svNumber,svFloat,svOctal
" syn match	svNumber	display contained "\d\+\(u\=l\{0,2}\|ll\=u\)\>"
" "hex number
" syn match	svNumber	display contained "0x\x\+\(u\=l\{0,2}\|ll\=u\)\>"
" syn match   svNumber "\(\<[0-9]\+\|\)'[bdoh][0-9a-fxzA-FXZ_]\+\>"
syn match	svNumber 	"\<\(\<[0-9]\+\)\?\('[bdoh]\)\?[0-9a-fxz_]\+\>"
" syn match   svNumber "\<[+-]\=[0-9]\+\>"
" Flag the first zero of an octal number as something special
syn match	svOctal		display contained "0\o\+\(u\=l\{0,2}\|ll\=u\)\>" contains=svOctalZero
syn match	svOctalZero	display contained "\<0"
syn match	svFloat		display contained "\d\+f"
"floating point number, with dot, optional exponent
syn match	svFloat		display contained "\d\+\.\d*\(e[-+]\=\d\+\)\=[fl]\="
"floating point number, starting with a dot, optional exponent
syn match	svFloat		display contained "\.\d\+\(e[-+]\=\d\+\)\=[fl]\=\>"
"floating point number, without dot, with exponent
syn match	svFloat		display contained "\d\+e[-+]\=\d\+[fl]\=\>"
"hexadecimal floating point number, optional leading digits, with dot, with exponent
syn match	svFloat		display contained "0x\x*\.\x\+p[-+]\=\d\+[fl]\=\>"
"hexadecimal floating point number, with leading digits, optional dot, with exponent
syn match	svFloat		display contained "0x\x\+\.\=p[-+]\=\d\+[fl]\=\>"

" flag an octal number with wrong digits
syn match	svOctalError	display contained "0\o*[89]\d*"
syn case match

let sv_comment_strings = 1

if exists("sv_comment_strings")
  " A comment can contain svString, svCharacter and svNumber.
  " But a "*/" inside a svString in a svComment DOES end the comment!  So we
  " need to use a special type of svString: svCommentString, which also ends on
  " "*/", and sees a "*" at the start of the line as comment again.
  " Unfortunately this doesn't work very well for // type of comments :-(
  syntax match	svCommentSkip		contained "^\s*\*\($\|\s\+\)"
  syntax region svCommentString		contained start=+L\=\\\@<!"+ skip=+\\\\\|\\"+ end=+"+ end=+\*/+me=s-1 contains=svSpecial,svCommentSkip
  syntax region svComment2String	contained start=+\\\@<!"+ skip=+\\\\\|\\"+ end=+"+ end="$" contains=svSpecial
  syntax region	svCommentL		start="//" skip="\\$" end="$" keepend contains=@svCommentGroup,svComment2String,svCharacter,svNumbersCom,svSpaceError,@Spell
  if exists("sv_no_comment_fold")
    syntax region svComment	matchgroup=svCommentStart start="/\*" end="\*/" contains=@svCommentGroup,svCommentStartError,svCommentString,svCharacter,svNumbersCom,svSpaceError,@Spell
  else
    syntax region svComment	matchgroup=svCommentStart start="/\*" end="\*/" contains=@svCommentGroup,svCommentStartError,svCommentString,svCharacter,svNumbersCom,svSpaceError,@Spell fold
  endif
else
  syn region	svCommentL	start="//" skip="\\$" end="$" keepend contains=@svCommentGroup,svSpaceError,@Spell
  if exists("sv_no_comment_fold")
    syn region	svComment	matchgroup=svCommentStart start="/\*" end="\*/" contains=@svCommentGroup,svCommentStartError,svSpaceError,@Spell
  else
    syn region	svComment	matchgroup=svCommentStart start="/\*" end="\*/" contains=@svCommentGroup,svCommentStartError,svSpaceError,@Spell fold
  endif
endif
" keep a // comment separately, it terminates a preproc. conditional
syntax match	svCommentError		display "\*/"
syntax match	svCommentStartError 	display "/\*"me=e-1 contained

" syntax region	svBlock		start="{" end="}" transparent fold
syntax region	svBlock		start="begin" end="end" transparent fold

" sv pre-defined constants
syn keyword svConstant	ALL ANY BAD_STATE BAD_TRANS CALL CHECK CHGEDGE
syn keyword svConstant	CLEAR COPY_NO_WAIT COPY_WAIT CROSS CROSS_TRANS
syn keyword svConstant	DEBUG DELETE EC_ARRAYX EC_CODE_END EC_CONFLICT
syn keyword svConstant	EC_EVNTIMOUT EC_EXPECT EC_FULLEXPECT EC_MBXTMOUT
syn keyword svConstant	EC_NEXPECT EC_RETURN EC_RGNTMOUT EC_SCONFLICT
syn keyword svConstant	EC_SEMTMOUT EC_SEXPECT EC_SFULLEXPECT EC_SNEXTPECT
syn keyword svConstant	EC_USERSET EQ EVENT FAIL FIRST FORK GE GOAL GT
syn keyword svConstant	HAND_SHAKE HI HIGH HNUM LE LIC_EXIT LIC_PRERR
syn keyword svConstant	LIC_PRWARN LIC_WAIT LO LOAD LOW LT MAILBOX MAX_COM
syn keyword svConstant	NE NEGEDGE NEXT NO_OVERLAP NO_OVERLAP_STATE
syn keyword svConstant	NO_OVERLAP_TRANS NO_VARS NO_WAIT NUM NUM_BIN
syn keyword svConstant	NUM_DET null OFF OK OK_LAST ON ONE_BLAST ONE_SHOT ORDER
syn keyword svConstant	PAST_IT PERCENT POSEDGE PROGRAM RAWIN REGION REPORT
syn keyword svConstant	SAMPLE SAVE SEMAPHORE SET SILENT STATE stderr
syn keyword svConstant	stdin stdout STR STR_ERR_OUT_OF_RANGE
syn keyword svConstant	STR_ERR_REGEXP_SYNTAX SUM TRANS VERBOSE void WAIT
syn keyword svConstant	__LINE__ __FILE__ __DATE__ __TIME__ 
syn keyword svConstant	__VERSION__ 

syn match   svUserConstant "\<[A-Z][A-Z0-9_]\+\>"
syn match   svUvmMacro  "`uvm_\w\+"

syn match svClass 	"\zs\w\+\ze::"
syn match svClass 	"\zs\w\+\ze\s\+\w\+\s*[=;,)\[]" contains=svConstant,svUserConstant
syn match svClass 	"\zs\w\+\ze\s\+\w\+\s*$" contains=svConstant,svUserConstant
syn match svClass 	"\zs\w\+\ze\s*#(" contains=svConstant,svUserConstant
syn match svUserMethod 	"\zs\w\+\ze\s*(" contains=svConstant,svUserConstant
syn match svObject 	"\zs\w\+\ze\.\w"
syn match svObject 	"\zs\w\+\ze\.\$\w"

" Accept ` for # (Verilog)
syn region	svPreCondit	start="^\s*\(`\|#\)\s*\(if\|ifdef\|ifndef\|elif\)\>" skip="\\$" end="$" end="//"me=s-1 contains=svComment,svCppString,svCharacter,svCppParen,svParenError,svNumbers,svCommentError,svSpaceError
syn match	svPreCondit	display "^\s*\(`\|#\)\s*\(else\|endif\)\>"
if !exists("sv_no_if0")
  syn region	svCppOut	start="^\s*\(`\|#\)\s*if\s\+0\+\>" end=".\@=\|$" contains=svCppOut2
  syn region	svCppOut2	contained start="0" end="^\s*\(`\|#\)\s*\(endif\>\|else\>\|elif\>\)" contains=svSpaceError,svCppSkip
  syn region	svCppSkip	contained start="^\s*\(`\|#\)\s*\(if\>\|ifdef\>\|ifndef\>\)" skip="\\$" end="^\s*\(`\|#\)\s*endif\>" contains=svSpaceError,svCppSkip
endif
syn region	svIncluded	display contained start=+"+ skip=+\\\\\|\\"+ end=+"+
syn match	svIncluded	display contained "<[^>]*>"
syn match	svInclude	display "^\s*\(`\|#\)\s*include\>\s*["<]" contains=svIncluded
"syn match svLineSkip	"\\$"
syn cluster	svPreProcGroup	contains=svPreCondit,svIncluded,svInclude,svDefine,svErrInParen,svErrInBracket,svUserLabel,svSpecial,svOctalZero,svCppOut,svCppOut2,svCppSkip,svFormat,svNumber,svFloat,svOctal,svOctalError,svNumbersCom,svString,svCommentSkip,svCommentString,svComment2String,@svCommentGroup,svCommentStartError,svParen,svBracket,svMulti
syn region	svDefine	start="^\s*\(`\|#\)\s*\(define\|undef\)\>" skip="\\$" end="$" end="//"me=s-1 contains=ALLBUT,@svPreProcGroup,@Spell
syn region	svPreProc	start="^\s*\(`\|#\)\s*\(pragma\>\|line\>\|warning\>\|error\>\)" skip="\\$" end="$" keepend contains=ALLBUT,@svPreProcGroup,@Spell

" Highlight User Labels
syn cluster	svMultiGroup	contains=svIncluded,svSpecial,svCommentSkip,svCommentString,svComment2String,@svCommentGroup,svCommentStartError,svUserCont,svUserLabel,svBitField,svOctalZero,svCppOut,svCppOut2,svCppSkip,svFormat,svNumber,svFloat,svOctal,svOctalError,svNumbersCom,svCppParen,svCppBracket,svCppString
syn region	svMulti		transparent start='?' skip='::' end=':' contains=ALLBUT,@svMultiGroup,@Spell
" syn region	svMulti		transparent start='?' skip='::' end=':' contains=ALL
" The above causes svCppOut2 to catch on:
"    i = (isTrue) ? 0 : 1;
" which ends up commenting the rest of the file

" Avoid matching foo::bar() by requiring that the next char is not ':'
syn cluster	svLabelGroup	contains=svUserLabel
syn match	svUserCont	display "^\s*\I\i*\s*:$" contains=@svLabelGroup
syn match	svUserCont	display ";\s*\I\i*\s*:$" contains=@svLabelGroup
syn match	svUserCont	display "^\s*\I\i*\s*:[^:]"me=e-1 contains=@svLabelGroup
syn match	svUserCont	display ";\s*\I\i*\s*:[^:]"me=e-1 contains=@svLabelGroup

syn match	svUserLabel	display "\I\i*" contained

" Avoid recognizing most bitfields as labels
syn match	svBitField	display "^\s*\I\i*\s*:\s*[1-9]"me=e-1
syn match	svBitField	display ";\s*\I\i*\s*:\s*[1-9]"me=e-1

if exists("sv_minlines")
  let b:sv_minlines = sv_minlines
else
  if !exists("sv_no_if0")
    let b:sv_minlines = 50	" #if 0 constructs can be long
  else
    let b:sv_minlines = 15	" mostly for () constructs
  endif
endif
exec "syn sync ccomment svComment minlines=" . b:sv_minlines

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_systemverilog_syn_inits")
  if version < 508
    let did_systemverilog_syn_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink svClass		Identifier
  HiLink svObject		Identifier
  HiLink svUserMethod		Function
  HiLink svUvmMacro		Function
  HiLink svTask                 Keyword
  HiLink svModifier		Tag
  HiLink svDeprecated		svError
  HiLink svMethods		Statement
  " HiLink svInterface		Label
  " HiLink svInterface		Function

  HiLink svFormat		svSpecial
  HiLink svCppString		svString
  HiLink svCommentL		svComment
  HiLink svCommentStart		svComment
  HiLink svLabel		Label
  HiLink svUserLabel		Label
  HiLink svConditional		Conditional
  HiLink svRepeat		Repeat
  HiLink svCharacter		Character
  HiLink svSpecialCharacter	svSpecial
  HiLink svNumber		Number
  HiLink svOctal		Number
  HiLink svOctalZero		PreProc	 " link this to Error if you want
  HiLink svFloat		Float
  HiLink svOctalError		svError
  HiLink svParenError		svError
  HiLink svErrInParen		svError
  HiLink svErrInBracket		svError
  HiLink svCommentError		svError
  HiLink svCommentStartError	svError
  HiLink svSpaceError		SpaceError
  HiLink svSpecialError		svError
  HiLink svOperator		Operator
  HiLink svStructure		Structure
  HiLink svInclude		Include
  HiLink svPreProc		PreProc
  HiLink svDefine		Macro
  HiLink svIncluded		svString
  HiLink svError		Error
  HiLink svStatement		Statement
  HiLink svPreCondit		PreCondit
  HiLink svType			Type
  " HiLink svConstant		Constant
  HiLink svConstant		Keyword
  HiLink svUserConstant		Constant
  HiLink svCommentString	svString
  HiLink svComment2String	svString
  HiLink svCommentSkip		svComment
  HiLink svString		String
  HiLink svComment		Comment
  HiLink svSpecial		SpecialChar
  HiLink svTodo			Todo
  HiLink svCppSkip		svCppOut
  HiLink svCppOut2		svCppOut
  HiLink svCppOut		Comment

  delcommand HiLink
endif

let b:current_syntax = "systemverilog"

" vim: ts=8

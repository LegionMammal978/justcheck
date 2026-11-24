$( Syntactic and logical types: rules 1 and 6. $)
$c ( ) -> = 0 wff class term |- |= |~ !- thm ?? junk $.
$v ph ps A B $.
wph $f wff ph $.
wps $f wff ps $.
cA $f class A $.
cB $f class B $.

$( ` term ` is a syntactic type with no variables, and there are three
   logical types.  The rest of the commands break rule 1. $)
$( $j syntax 'wff'; syntax 'class' 'term';
      syntax '|-' as 'wff'; syntax '|=' as 'wff'; syntax '|~' as 'term';
      syntax '|-' as 'class';
      syntax 'class' as 'wff';
      syntax '!-' as 'thm';
      syntax 'nonexistent';
      syntax 'ph';
      syntax 'nonexistent' as 'wff';
      syntax '|-' as 'nonexistent';
      primitive 'wi' 'weq' 't0'; $)

wi $a wff ( ph -> ps ) $.
weq $a wff A = B $.
t0 $a term 0 $.

$( Good: statements of each logical type, parsed as its corresponding type. $)
ok1 $a |- ( ph -> ph ) $.
ok2 $a |= ( ph -> A = B ) $.
ok3 $a |~ 0 $.
${
  ok4.1 $e |- ph $.
  ok4.2 $e |= ( ph -> ps ) $.
  ok4 $a |- ps $.
$}
ok5 $p |- ( A = A -> A = A ) $= cA cA weq ok1 $.

$( Rule 6: typecodes that are neither syntactic nor logical.  The command
   for ` !- ` was rejected. $)
bad6a $a !- ( ph -> ph ) $.
bad6b $a junk ph $.
${
  bad6c.1 $e junk ph $.
  bad6c $a |- ph $.
$}
$( An incomplete proof is still a statement. $)
bad6d $p ?? ph $= ? $.

$( Rule 6: statements that do not parse. $)
bad6e $a |- ( ph -> ) $.
bad6f $a |- ( ph -> ps $.
bad6g $a |- A $.
bad6h $a |- ph ps $.
bad6i $a |- $.
$( A term is not a wff, and a wff is not a term. $)
bad6j $a |- 0 $.
bad6k $a |~ A = B $.
${
  bad6l.1 $e |- ( A -> ph ) $.
  bad6l $a |- ph $.
$}
bad6m $p |- ( ph = ph ) $= ? $.

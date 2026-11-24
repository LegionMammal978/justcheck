$( Ambiguity: rule 5. $)
$c ( ) -> -. = =/= (/) suc !! wff class |- $.
$v ph ps A B $.
wph $f wff ph $.
wps $f wff ps $.
cA $f class A $.
cB $f class B $.

$( $j syntax 'wff' 'class'; syntax '|-' as 'wff';
      primitive 'wn' 'wi' 'wceq' 'wne' 'c0' 'csuc' 'csuc2'; $)
wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
wceq $a wff A = B $.
wne $a wff A =/= B $.
c0 $a class (/) $.
csuc $a class suc A $.

eqid $a |- A = A $.
nsuceq0 $a |- suc A =/= (/) $.
${
  neii.1 $e |- A =/= B $.
  neii $a |- -. A = B $.
$}
${
  pm2.24ii.1 $e |- ph $.
  pm2.24ii.2 $e |- -. ph $.
  pm2.24ii $a |- ps $.
$}
${
  a1ii.1 $e |- ph $.
  a1ii.2 $e |- ps $.
  a1ii $a |- ph $.
$}

$( A postfix operator, which makes ` suc (/) !! ` ambiguous.  No statement
   up to ` dfbad ` runs into that, and the definition is justified. $)
cbad $a class A !! $.
df-bad $a |- A !! = (/) $.
dfbad $p |- A !! = (/) $=
  cA cbad c0 wceq c0 c0 wceq cA df-bad c0 eqid a1ii $.

$( A proof of anything.  Each statement it uses is unambiguous, but
   ` suc (/) !! = (/) ` is read as ` ( suc (/) ) !! = (/) ` by ` dfbad ` and as
   ` suc ( (/) !! ) = (/) ` by ` nsuceq0 ` . $)
bad $p |- ph $=
  c0 csuc cbad c0 wceq wph
  c0 csuc dfbad
  c0 cbad csuc c0 c0 cbad nsuceq0 neii
  pm2.24ii $.

$( The same proof through lemmas that forget the parse trees.  Now the
   statements of the lemmas are ambiguous. $)
lem1 $p |- suc (/) !! = (/) $= c0 csuc dfbad $.
lem2 $p |- suc (/) !! =/= (/) $= c0 cbad nsuceq0 $.
bad2 $p |- ph $=
  c0 csuc cbad c0 wceq wph lem1
  c0 csuc cbad c0 lem2 neii
  pm2.24ii $.

$( Ambiguous hypotheses and axioms. $)
${
  bad3.1 $e |- suc A !! = B $.
  bad3 $a |- A = B $.
$}
bad4 $a |- ( ph -> suc (/) !! =/= (/) ) $.

$( Any use where the two operators do not meet is unambiguous. $)
ok1 $p |- suc A =/= (/) $= cA nsuceq0 $.
ok2 $p |- (/) !! !! = (/) $= c0 cbad dfbad $.

$( A syntax axiom that overlaps another one.  Its own statement is
   ambiguous, and so are a statement before it and one after it: every
   statement is parsed with the grammar of the whole database. $)
bad5 $p |- -. suc suc A = (/) $= cA csuc csuc c0 cA csuc nsuceq0 neii $.
csuc2 $a class suc suc A $.
bad6 $a |- suc suc A =/= (/) $.

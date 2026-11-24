$( The MIU system, where a wff is any string of the letters, including the
   empty one.  There are no errors. $)
$c M I U wff |- $.
$v x y $.
wx $f wff x $.
wy $f wff y $.
$( $j syntax 'wff'; syntax '|-' as 'wff'; primitive 'we' 'wM' 'wI' 'wU'; $)
we $a wff $.
wM $a wff x M $.
wI $a wff x I $.
wU $a wff x U $.

ax $a |- M I $.
${
  r1.1 $e |- x I $.
  r1 $a |- x I U $.
$}
${
  r2.1 $e |- x I I I $.
  r2 $a |- x U $.
$}
miu $p |- M I U $= we wM ax r1 $.
empty $a |- $.

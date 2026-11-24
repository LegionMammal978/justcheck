$( Classes are interpreted as the set of setvars occurring in them, so
   F x = { x }, and R A B says A and B share no setvar.  $d x A then makes
   ax-r valid.  R ( F h ) ( F h ) is false, so it is not provable without
   C. $)
$c ( ) -. = R F C wff setvar class |- $.
$v ph ps x z A B $.
wph $f wff ph $.
wps $f wff ps $.
vx $f setvar x $.
vz $f setvar z $.
cA $f class A $.
$( B is first declared as a setvar, in a closed block. $)
${ vB $f setvar B $. $}
cB $f class B $.

$( $j syntax 'wff'; syntax 'setvar'; syntax 'class'; syntax '|-' as 'wff';
      bound 'setvar';
      primitive 'wn' 'wceq' 'wr' 'cf';
      definition 'ax-cexp' for 'cc'; $)

wn $a wff -. ph $.
wceq $a wff A = B $.
wr $a wff R A B $.
cf $a class F x $.

${ ax-just.1 $e |- ph $.  ax-just.2 $e |- ps $.  ax-just $a |- ph $. $}
${ $d x A $.  ax-r $a |- R A F x $. $}
ax-irr $a |- -. R F x F x $.

cc $a class C $.
df-c $a |- R A C $.
$( Only the shape of the expansion statement matters: C := F x. $)
ax-cexp $a |- C = F x $.

$( Rule 25 should reject $d z B, since B is a class variable outside the
   arguments.  The checker looks up B's type from its first $f, a setvar. $)
${
  $d z B $.
  t1 $p |- R B C $=
    cB cc wr cB vz cf wr cB df-c vz cB ax-r ax-just $.
$}

$( An ordinary theorem.  Expanding C gives R ( F h ) ( F h ), which is false
   in the model. $)
t2 $p |- R C C $= cc t1 $.

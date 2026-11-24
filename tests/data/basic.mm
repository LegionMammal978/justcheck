$( A small database exercising the definition rules. $)
$c ( ) -> -. <-> /\ A. T. wff setvar |- $.
$v ph ps ch x y z $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
vx $f setvar x $.
vy $f setvar y $.
vz $f setvar z $.

$( $j syntax 'wff'; syntax 'setvar'; syntax '|-' as 'wff';
      bound 'setvar'; primitive 'wn' 'wi' 'wb' 'wal'; $)
wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
wb $a wff ( ph <-> ps ) $.
wal $a wff A. x ph $.

$( Axioms that make proofs easy; they need not be sound. $)
biid $a |- ( ph <-> ph ) $.
${
  ax-just.1 $e |- ph $.
  ax-just.2 $e |- ps $.
  ax-just $a |- ph $.
$}
ax-any $a |- ph $.

wa $a wff ( ph /\ ps ) $.
df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

$( A good justified theorem. $)
dfan $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
  wph wps wa wph wps wn wi wn wb
  wph wps wn wi wn wph wps wn wi wn wb
  wph wps df-an
  wph wps wn wi wn biid
  ax-just $.

$( Rule 24: the second subproof contains ` /\ ` . $)
bad24 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
  wph wps wa wph wps wn wi wn wb
  wph wps wa wph wps wa wb
  wph wps df-an
  wph wps wa biid
  ax-just $.

$( Rule 23: the second subproof's conclusion is not the expansion. $)
bad23a $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
  wph wps wa wph wps wn wi wn wb
  wph wph wb
  wph wps df-an
  wph biid
  ax-just $.

$( Rule 19: the constructor occurs with different arguments. $)
bad19 $p |- ( ( ( ph /\ ps ) /\ ch ) <-> -. ( ( ph /\ ps ) -> -. ch ) ) $=
  wph wps wa wch wa wph wps wa wch wn wi wn wb
  wph wps wa wch wn wi wn wph wps wa wch wn wi wn wb
  wph wps wa wch df-an
  wph wps wa wch wn wi wn wph wps wa wch wn wi wn wb ax-any
  ax-just $.

$( Rule 8. $)
${
  $d ph ps $.
  bad8 $a |- ( ph -> ps ) $.
$}

$( A definition with hidden variables of both kinds. $)
wtru $a wff T. $.
df-tru $a |- ( T. <-> A. x ( ph -> ph ) ) $.
wT. $p wff T. $= wtru $.

$( Good: fresh dummy variables ` y ` and ` ps ` . $)
dftru $p |- ( T. <-> A. x ( ph -> ph ) ) $=
  wtru wph wph wi vx wal wb
  wps wps wi vy wal wph wph wi vx wal wb
  wph vx df-tru
  wps wps wi vy wal wph wph wi vx wal wb ax-any
  ax-just $.

$( Rule 23: ` x ` replaces a hidden variable but occurs in the conclusion,
   so it is not a dummy variable. $)
bad23b $p |- ( T. <-> A. x ( ph -> ph ) ) $=
  wtru wph wph wi vx wal wb
  wps wps wi vx wal wph wph wi vx wal wb
  wph vx df-tru
  wps wps wi vx wal wph wph wi vx wal wb ax-any
  ax-just $.

$( Rule 16: two definition axioms. $)
bad16 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
  wph wps wa wph wps wn wi wn wb
  wtru wph wph wi vx wal wb
  wph wps df-an
  wph vx df-tru
  ax-just $.

$( Rule 25: dummy variable ` y ` is disjoint from ` ch ` , which is outside the
   (empty) arguments. $)
${
  $d y ch $.
  bad25 $p |- ( T. <-> A. x ( ch -> ch ) ) $=
    wtru wch wch wi vx wal wb
    wps wps wi vy wal wch wch wi vx wal wb
    wch vx df-tru
    wps wps wi vy wal wch wch wi vx wal wb ax-any
    ax-just $.
$}

$( Good: a DV restriction with a variable of bound type is allowed. $)
${
  $d y x $.
  ok25 $p |- ( T. <-> A. x ( ch -> ch ) ) $=
    wtru wch wch wi vx wal wb
    wps wps wi vy wal wch wch wi vx wal wb
    wch vx df-tru
    wps wps wi vy wal wch wch wi vx wal wb ax-any
    ax-just $.
$}

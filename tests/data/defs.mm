$( Definition-level rules, and the remaining justified theorem rules. $)
$c ( ) -> -. <-> /\ <=> A. T. TOP P N W S L E Q R V D Z [ ] ~ X Y J K H $.
$c wff setvar |- $.
$v ph ps ch x y $.
wph $f wff ph $.
wps $f wff ps $.
wch $f wff ch $.
vx $f setvar x $.
vy $f setvar y $.

$( $j syntax 'wff'; syntax 'setvar'; syntax '|-' as 'wff';
      bound 'setvar' 'nonexistent' 'TOP' 'ph';
      primitive 'wn' 'wi' 'wb' 'wal' 'wtop' 'wprim' 'wdup' 'vnew' 'nolabel'
        'biid';
      definition 'dfbi2' for 'wbi2';
      definition 'nonexistent' for 'wfour';
      definition 'dfx' for 'wn';
      definition 'df-an' for 'nosuch';
      definition 'df-an' for 'wbi2'; $)

wn $a wff -. ph $.
wi $a wff ( ph -> ps ) $.
wb $a wff ( ph <-> ps ) $.
wal $a wff A. x ph $.
wtop $a wff TOP $.

biid $a |- ( ph <-> ph ) $.
${
  ax-just.1 $e |- ph $.
  ax-just.2 $e |- ps $.
  ax-just $a |- ph $.
$}
${
  ax-imp.1 $e |- ph $.
  ax-imp.2 $e |- ps $.
  ax-imp $a |- ( ph -> ph ) $.
$}
ax-any $a |- ph $.

$( Rule 9. $)
wdup $a wff [ ph ph ] $.
$( Rule 7. $)
vnew $a setvar ~ $.

wa $a wff ( ph /\ ps ) $.
df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

$( Rule 11: primitive with a definition. $)
wprim $a wff P ph $.
df-prim $a |- ( P ph <-> ph ) $.
$( Rule 10: no definition. $)
wnodef $a wff N ph $.
$( Rule 11: two definitions. $)
wtwo $a wff W ph $.
df-two1 $a |- ( W ph <-> ph ) $.
df-two2 $a |- ( W ph <-> -. -. ph ) $.
$( Rule 4: the target does not exist. $)
wfour $a wff L ph $.
df-four $a |- ( L ph <-> ph ) $.
$( Rule 12. $)
wtwelve $a wff E ph $.
df-twelve $a |- -. ( E ph -> ph ) $.
$( Rule 13. $)
wthirteen $a wff Q ph ps $.
df-thirteen $a |- ( Q ph ph <-> ph ) $.
$( Rule 15. $)
wfifteen $a wff R x y $.
${
  $d x y $.
  df-fifteen $a |- ( R x y <-> A. x A. y TOP ) $.
$}
$( Rule 14. $)
wfourteen $a wff V ph $.
df-fourteen $a |- ( V ph <-> -. V ph ) $.

$( A definition whose expansion comes from a definition command. $)
wbi2 $a wff ( ph <=> ps ) $.
df-bi2 $a |- -. ( ( ( ph <=> ps ) -> ( ph -> ps ) )
                 -> -. ( ( ph -> ps ) -> ( ph <=> ps ) ) ) $.
bi2just $p |- -. ( ( ( ph <=> ps ) -> ( ph -> ps ) )
                  -> -. ( ( ph -> ps ) -> ( ph <=> ps ) ) ) $=
  wph wps wbi2 wph wps wi wi wph wps wi wph wps wbi2 wi wn wi wn
  wph wps wi wph wps wi wi wph wps wi wph wps wi wi wn wi wn
  wph wps df-bi2
  wph wps wi wph wps wi wi wph wps wi wph wps wi wi wn wi wn ax-any
  ax-just $.
dfbi2 $p |- ( ( ph <=> ps ) <-> ( ph -> ps ) ) $=
  wph wps wbi2 wph wps wi wb ax-any $.

$( Rule 22 with a hypothesis. $)
wcond $a wff D ph $.
${
  df-cond.1 $e |- ph $.
  df-cond $a |- ( D ph <-> ph ) $.
$}
${
  good22.1 $e |- ph $.
  good22 $p |- ( D ph <-> ph ) $=
    wph wcond wph wb wph wph wb wph good22.1 df-cond wph biid ax-just $.
$}
bad22b $p |- ( D ph <-> ph ) $=
  wph wcond wph wb wph wph wb wph wph ax-any df-cond wph biid ax-just $.

$( Rule 18. $)
${
  bad18.1 $e |- ( ph /\ ps ) $.
  bad18 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
    wph wps wa wph wps wn wi wn wb
    wph wps wn wi wn wph wps wn wi wn wb
    wph wps df-an
    wph wps wn wi wn biid
    ax-just $.
$}

$( Rule 20. $)
bad20 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $= wph wps df-an $.

$( Rule 21 (and 23). $)
bad21 $p |- ( ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )
              -> ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) ) $=
  wph wps wa wph wps wn wi wn wb
  wph wps wn wi wn wph wps wn wi wn wb
  wph wps df-an
  wph wps wn wi wn biid
  ax-imp $.

$( Rule 22: a step between the final step and the definition axiom. $)
bad22 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
  wph wps wa wph wps wn wi wn wb
  wph wps wn wi wn wph wps wn wi wn wb
    wph wps wa wph wps wn wi wn wb
    wph wps wn wi wn wph wps wn wi wn wb
    wph wps df-an
    wph wps wn wi wn biid
    ax-just
  wph wps wn wi wn biid
  ax-just $.

$( Incomplete proof. $)
inc $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
  wph wps wa wph wps wn wi wn wb ? wph wps df-an ? ax-just $.

$( Rule 23: a hidden variable is replaced by a constant. $)
wtru $a wff T. $.
df-tru $a |- ( T. <-> A. x ( ph -> ph ) ) $.
bad23 $p |- ( T. <-> A. x ( ph -> ph ) ) $=
  wtru wph wph wi vx wal wb
  wtop wtop wi vy wal wph wph wi vx wal wb
  wph vx df-tru
  wtop wtop wi vy wal wph wph wi vx wal wb ax-any
  ax-just $.

$( Rule 17: the justified theorem contains syntax defined later ( ` T. ` is
   defined after ` /\ ` ). $)
bad17 $p |- ( ( T. /\ ps ) <-> -. ( T. -> -. ps ) ) $=
  wtru wps wa wtru wps wn wi wn wb
  wtru wps wn wi wn wtru wps wn wi wn wb
  wtru wps df-an
  wtru wps wn wi wn biid
  ax-just $.

$( Rule 14: syntax axioms order the constructors.  ` Y ` is declared before
   ` X ` , so ` X ` is defined later and may not occur in its definition, even
   though the definition of ` X ` comes first. $)
wy $a wff Y $.
wx $a wff X $.
df-x $a |- ( X <-> TOP ) $.
df-y $a |- ( Y <-> X ) $.

$( Rule 11: ` J ` and ` K ` are first contained in the same definition. $)
wj $a wff J $.
wk $a wff K $.
df-jk $a |- ( J <-> K ) $.

$( Rule 11: ` H ` is first contained in a definition's hypothesis, so that is
   its associated definition, not the later one with ` H ` in its conclusion. $)
wh $a wff H $.
${
  df-h1.1 $e |- H $.
  df-h1 $a |- TOP $.
$}
df-h2 $a |- ( H <-> TOP ) $.

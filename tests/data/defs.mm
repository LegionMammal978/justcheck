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
      definition 'nonexistent' for 'wthree';
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

$( Rule 7. $)
wdup $a wff [ ph ph ] $.
$( Rule 5. $)
vnew $a setvar ~ $.

wa $a wff ( ph /\ ps ) $.
df-an $a |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $.

$( Rule 9: primitive with a definition. $)
wprim $a wff P ph $.
df-prim $a |- ( P ph <-> ph ) $.
$( Rule 8: no definition. $)
wnodef $a wff N ph $.
$( Rule 9: two definitions. $)
wtwo $a wff W ph $.
df-two1 $a |- ( W ph <-> ph ) $.
df-two2 $a |- ( W ph <-> -. -. ph ) $.
$( Rule 3: the target does not exist. $)
wthree $a wff L ph $.
df-three $a |- ( L ph <-> ph ) $.
$( Rule 10. $)
wten $a wff E ph $.
df-ten $a |- -. ( E ph -> ph ) $.
$( Rule 11. $)
weleven $a wff Q ph ps $.
df-eleven $a |- ( Q ph ph <-> ph ) $.
$( Rule 13. $)
wthirteen $a wff R x y $.
${
  $d x y $.
  df-thirteen $a |- ( R x y <-> A. x A. y TOP ) $.
$}
$( Rule 12. $)
wtwelve $a wff V ph $.
df-twelve $a |- ( V ph <-> -. V ph ) $.

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

$( Rule 20 with a hypothesis. $)
wcond $a wff D ph $.
${
  df-cond.1 $e |- ph $.
  df-cond $a |- ( D ph <-> ph ) $.
$}
${
  good20.1 $e |- ph $.
  good20 $p |- ( D ph <-> ph ) $=
    wph wcond wph wb wph wph wb wph good20.1 df-cond wph biid ax-just $.
$}
bad20b $p |- ( D ph <-> ph ) $=
  wph wcond wph wb wph wph wb wph wph ax-any df-cond wph biid ax-just $.

$( Rule 16. $)
${
  bad16.1 $e |- ( ph /\ ps ) $.
  bad16 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
    wph wps wa wph wps wn wi wn wb
    wph wps wn wi wn wph wps wn wi wn wb
    wph wps df-an
    wph wps wn wi wn biid
    ax-just $.
$}

$( Rule 18. $)
bad18 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $= wph wps df-an $.

$( Rule 19 (and 21). $)
bad19 $p |- ( ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) )
              -> ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) ) $=
  wph wps wa wph wps wn wi wn wb
  wph wps wn wi wn wph wps wn wi wn wb
  wph wps df-an
  wph wps wn wi wn biid
  ax-imp $.

$( Rule 20: a step between the final step and the definition axiom. $)
bad20 $p |- ( ( ph /\ ps ) <-> -. ( ph -> -. ps ) ) $=
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

$( Rule 21: a hidden variable is replaced by a constant. $)
wtru $a wff T. $.
df-tru $a |- ( T. <-> A. x ( ph -> ph ) ) $.
bad21 $p |- ( T. <-> A. x ( ph -> ph ) ) $=
  wtru wph wph wi vx wal wb
  wtop wtop wi vy wal wph wph wi vx wal wb
  wph vx df-tru
  wtop wtop wi vy wal wph wph wi vx wal wb ax-any
  ax-just $.

$( Rule 15: the justified theorem contains syntax defined later ( ` T. ` is
   defined after ` /\ ` ). $)
bad15 $p |- ( ( T. /\ ps ) <-> -. ( T. -> -. ps ) ) $=
  wtru wps wa wtru wps wn wi wn wb
  wtru wps wn wi wn wtru wps wn wi wn wb
  wtru wps df-an
  wtru wps wn wi wn biid
  ax-just $.

$( Definitions order the constructors: ` Y ` is declared before ` X ` but
   defined after it, so ` X ` may occur in its definition. $)
wy $a wff Y $.
wx $a wff X $.
df-x $a |- ( X <-> TOP ) $.
df-y $a |- ( Y <-> X ) $.

$( Rule 9: ` J ` and ` K ` are first contained in the same definition. $)
wj $a wff J $.
wk $a wff K $.
df-jk $a |- ( J <-> K ) $.

$( Rule 9: ` H ` is first contained in a definition's hypothesis, so that is
   its associated definition, not the later one with ` H ` in its conclusion. $)
wh $a wff H $.
${
  df-h1.1 $e |- H $.
  df-h1 $a |- TOP $.
$}
df-h2 $a |- ( H <-> TOP ) $.

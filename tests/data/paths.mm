$( A fragment of the grammar of set.mm, whose garden paths need no hints,
   with variables whose type depends on the scope and with syntax theorems.
   There are no errors. $)
$c ( ) -> /\ = e. { } <. >. , | |-> X. Lim wff class setvar |- $.
$v ph ps x y z A B C R $.
wph $f wff ph $.
wps $f wff ps $.
cA $f class A $.
cB $f class B $.
cC $f class C $.
cR $f class R $.

$( ` x ` is a class in this block, and a setvar afterwards. $)
${
  cx $f class x $.
  limx $a |- Lim x $.
$}
vx $f setvar x $.
vy $f setvar y $.
vz $f setvar z $.

$( $j syntax 'wff'; syntax '|-' as 'wff'; bound 'setvar';
      primitive 'wi' 'wa' 'wceq' 'wcel' 'wbr' 'wlim' 'cv' 'csn' 'cop' 'cotp'
        'copab' 'coprab' 'cmpt' 'cxp' 'co'; $)
wi $a wff ( ph -> ps ) $.
wa $a wff ( ph /\ ps ) $.
wceq $a wff A = B $.
wcel $a wff A e. B $.
wbr $a wff A R B $.
wlim $a wff Lim A $.
cv $a class x $.
csn $a class { A } $.
cop $a class <. A , B >. $.
cotp $a class <. A , B , C >. $.
copab $a class { <. x , y >. | ph } $.
coprab $a class { <. <. x , y >. , z >. | ph } $.
cmpt $a class ( x e. A |-> B ) $.
cxp $a class ( A X. B ) $.
co $a class ( A R B ) $.

id $a |- ( ph -> ph ) $.
eqid $a |- A = A $.

$( Syntax theorems, and their use in a proof. $)
wel $p wff x e. y $= vx cv vy cv wcel $.
weq $p wff x = y $= vx cv vy cv wceq $.
elid $p |- ( x e. y -> x e. y ) $= vx vy wel id $.
eqeq $p |- ( x = y -> x = y ) $= vx vy weq id $.

$( ` ( x e. A ` starts a mapping, a conjunction and an operation value. $)
p1 $p |- ( x e. A |-> B ) = ( x e. A |-> B ) $= cA cB vx cmpt eqid $.
p2 $p |- ( ( x e. A /\ ph ) -> ( x e. A /\ ph ) ) $=
  vx cv cA wcel wph wa id $.
p3 $p |- ( x X. A ) = ( x X. A ) $= vx cv cA cxp eqid $.
p4 $p |- ( x y z ) = ( x y z ) $= vx cv vz cv vy cv co eqid $.
p5 $p |- ( x y z -> x y z ) $= vx cv vz cv vy cv wbr id $.

$( ` { <. ` and ` { <. <. ` start class abstractions and singletons. $)
p6 $p |- { <. x , y >. | ph } = { <. x , y >. | ph } $= wph vx vy copab eqid $.
p7 $p |- { <. x , y >. } = { <. x , y >. } $= vx cv vy cv cop csn eqid $.
p8 $p |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , z >. | ph } $=
  wph vx vy vz coprab eqid $.
p9 $p |- { <. <. x , y >. , z >. } = { <. <. x , y >. , z >. } $=
  vx cv vy cv cop vz cv cop csn eqid $.
p10 $p |- { <. <. x , A >. , B >. } = { <. <. x , A >. , B >. } $=
  vx cv cA cop cB cop csn eqid $.
p11 $p |- ( A = { <. <. x , B >. , C >. } -> A = { <. <. x , B >. , C >. } ) $=
  cA vx cv cB cop cC cop csn wceq id $.
p12 $p |- { <. <. x , y , z >. , A >. } = { <. <. x , y , z >. , A >. } $=
  vx cv vy cv vz cv cotp cA cop csn eqid $.

$( The axiom from the block where ` x ` is a class. $)
p13 $p |- Lim { A } $= cA csn limx $.

$( A database of equations.  ` wff ` is a syntactic type with no variables,
   whose only constructor is equality, and a class constructor is defined
   through it. $)
$c = (/) suc 1 2 wff class |- $.
$v A B C D $.
cA $f class A $.
cB $f class B $.
cC $f class C $.
cD $f class D $.

$( $j syntax 'wff'; syntax '|-' as 'wff'; primitive 'weq' 'c0' 'csuc'; $)
weq $a wff A = B $.
c0 $a class (/) $.
csuc $a class suc A $.

eqid $a |- A = A $.
${
  eqtr.1 $e |- A = B $.
  eqtr.2 $e |- B = C $.
  eqtr $a |- A = C $.
$}
${
  suceq.1 $e |- A = B $.
  suceq $a |- suc A = suc B $.
$}
${
  just.1 $e |- A = B $.
  just.2 $e |- C = D $.
  just $a |- A = B $.
$}

c1 $a class 1 $.
df-1 $a |- 1 = suc (/) $.
df1 $p |- 1 = suc (/) $=
  c1 c0 csuc c0 csuc c0 csuc df-1 c0 csuc eqid just $.

c2 $a class 2 $.
df-2 $a |- 2 = suc 1 $.
df2 $p |- 2 = suc 1 $=
  c2 c1 csuc c1 csuc c1 csuc df-2 c1 csuc eqid just $.

2eq $p |- 2 = suc suc (/) $=
  c2 c1 csuc c0 csuc csuc df2 c1 c0 csuc df1 suceq eqtr $.

$( Rule 23 (and 24): the rules for justified theorems are enforced here as
   anywhere else. $)
bad23 $p |- 2 = suc 1 $=
  c2 c1 csuc c2 c2 df-2 c2 eqid just $.

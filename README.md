# justcheck

This is a definition checker for Metamath databases, ensuring that all definitional extensions are *conservative* (a definition does not permit any theorems to be proven with fewer axioms) and *eliminable* (any statement or proof using the definition can be mechanically replaced with a statement without it). You should run it as `justcheck <DATABASE> [TARGETS] [--defs <PATTERN>] [--exclude <PATTERN>]`. `DATABASE` is the Metamath database to check. `TARGETS` is the pattern of definition axioms to check: the default is `*`, matching all definitions. `--defs` specifies the pattern of labels to treat as definitions: the default is `df-*`. `--exclude` specifies a set of labels to exclude from the `--defs` pattern, for databases with special definition forms that cannot be handled by these rules.

To check `set.mm`, this checker can be invoked as `justcheck set.mm --exclude df-clab,df-cleq,df-clel`.

## Terminology

- A *variable type* is a typecode that appears in an `$f` statement.
- A *bound type* is a variable type that appears in a `$j bound 'TYPECODE';` command.
- A *syntax axiom* is an `$a` statement with a typecode of variable type, defining a new *syntax constructor*.
- A statement *contains* a syntax constructor when it appears in the hypotheses or conclusion. A proof or subproof *contains* a syntax constructor when it appears in any step.
- A syntax constructor is *primitive* if its axiom appears in a `$j primitive 'SYNTAX';` command; otherwise, it is *defined*.
- A *definition axiom* is an `$a` statement whose label matches `df-*` (or another pattern as configured in `--defs`).
- The *associated definition* of a defined syntax constructor is the first definition axiom in the database containing that syntax constructor.
- A defined syntax constructor is *defined later* than another when its associated definition appears later in the database.
- The *expansion statement* of a defined syntax constructor is a `$a` or `$p` statement referred to by a `$j definition 'DEFTHM' for 'SYNTAX';` command if one is present; otherwise, the expansion statement is the associated definition. It defines an *expansion* with a *definiendum* (LHS) and a *definiens* (RHS).
- The *hidden variables* of an expansion are those that appear in the definiens (RHS) but not in the definiendum (LHS).
- A *justified theorem* of a definition axiom is any `$p` statement that directly uses the axiom, with an *associated constructor* corresponding to the definition axiom.
- A *dummy variable* in a theorem is a variable that is contained in its proof but not in its `$e` hypotheses or conclusion.

## Rules

1. A `$j bound` command's `TYPECODE` must be a math constant.
2. A `$j primitive` command's `SYNTAX` must refer to a syntax constructor.
3. A `$j definition` command's `SYNTAX` must refer to the axiom for a defined syntax constructor, and its `DEFTHM` must refer to an `$a` or `$p` statement. There must not be multiple `$j definition` commands for the same syntax constructor.
4. The syntax constructors must form an unambiguous grammar.
5. A syntax axiom must not have a bound type as its typecode.
6. `$a` and `$p` statements must not have any mandatory DV restrictions between variables of non-bound type.
7. A syntax axiom must not have any `$e` hypotheses or DV restrictions, and it must not contain any variable more than once.
8. Every defined syntax constructor must have an associated definition.
9. Every definition axiom must be the associated definition of exactly one syntax constructor.
10. An expansion statement must have a conclusion of form `typecode ( LHS root RHS )`, where the `root` is some syntax constructor with two arguments. The first argument `LHS` is the definiendum, and the second argument `RHS` is the definiens.
11. The definiendum (LHS) of an expansion must match its literal syntax constructor with a different variable for each argument.
12. The definiens (RHS) of an expansion must not contain its own syntax constructor nor any later-defined constructor.
13. An expansion statement must have no DV restrictions between variables appearing in the definiendum (LHS).
14. A `$p` statement must directly use at most one definition axiom, in which case it is a justified theorem of that definition axiom.
15. A justified theorem and its proof must not contain any syntax constructor defined later than the associated constructor.
16. A justified theorem must not have any `$e` hypotheses containing the associated constructor.
17. In the conclusion of a justified theorem, every occurrence of the associated constructor must have the same arguments.
18. In the proof of a justified theorem, the final step must have exactly two `$e` hypotheses, satisfied by two subproofs.
19. The first subproof's conclusion must match the final step's conclusion verbatim.
20. The first subproof must end in an instance of the definition axiom, with each `$e` hypothesis satisfied by an `$e` hypothesis of the theorem.
21. The second subproof's conclusion must match a valid result of the following process: Take the final step's conclusion, and match the arguments of the associated constructor against its definiendum (LHS). Replace it with its definiens (RHS), where each hidden variable is replaced with a fresh dummy variable. Each hidden variable must be replaced with a different dummy variable.
22. The second subproof must not contain the associated constructor or its definition axiom.
23. If a justified theorem has a DV condition involving a fresh dummy variable used in the replaced definiens (RHS), and the other variable is a non-dummy variable of non-bound type, then the other variable must appear in the arguments of the associated constructor.

## Database usage

Conventionally, each definition axiom should be followed by a *justified restatement*, identical to the definition axiom. Its proof should end in `a1ii |- ph & |- ps => |- ph` or an equivalent, where the first branch is simply the definition axiom itself, and the second branch contains the same statement with the new syntax replaced with its definition. Any hidden variables in the definition should be replaced with fresh dummy variables. This ensures that no matter what the hidden variables are actually substituted with, the axiom is justifiable with the axioms used by the sceond branch. For example, here is `df-sb` and its justified restatement `dfsb`:

```
  ${
    $d x y $.  $d t y $.  $d ph y $.
    $( Define proper substitution.  [...]  Proofs should use ~ dfsb instead.
       (New usage is discouraged.) $)
    df-sb $a |- ( [ t / x ] ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) ) $.

    $d x z $.  $d y z $.  $d t z $.  $d ph z $.
    $( Justified restatement of ~ df-sb .
       (Proof modification is discouraged.) $)
    dfsb $p |- ( [ t / x ] ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) ) $=
      ( vz wsb weq wi wal wb equequ1 equequ2 imbi1d albidv imbi12d cbvalvw a1ii
      df-sb ) ABDFCDGZBCGZAHZBIZHZCIZJEDGZBEGZAHZBIZHZEIUDJABCDRUIUCECECGZUESUH
      UBECDKUJUGUABUJUFTAECBLMNOPQ $.
  $}
```

The proof of `dfsb` is a `cbvalvw` instance, to swap out the hidden variable `y` for the fresh dummy variable `z`:

```
38   a1ii.1=df-sb      $a |- ( [ t / x ] ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) )
53       imbi12d.1=equequ1 $p |- ( z = y -> ( z = t <-> y = t ) )
65           imbid.1=equequ2   $p |- ( z = y -> ( x = z <-> x = y ) )
66         albidv.1=imbi1d   $p |- ( z = y -> ( ( x = z -> ph ) <-> ( x = y -> ph ) ) )
67       imbi12d.2=albidv  $p |- ( z = y -> ( A. x ( x = z -> ph ) <-> A. x ( x = y -> ph ) ) )
68     cbvalvw.1=imbi12d $p |- ( z = y -> ( ( z = t -> A. x ( x = z -> ph ) ) <-> ( y = t -> A. x ( x = y -> ph ) ) ) )
69   a1ii.2=cbvalvw    $p |- ( A. z ( z = t -> A. x ( x = z -> ph ) ) <-> A. y ( y = t -> A. x ( x = y -> ph ) ) )
70 dfsb=a1ii         $p |- ( [ t / x ] ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) )
```

The proof requires `ax-mp` through `ax-7`. For definitions with no hidden variables, the second subproof can be satisfied with a trivial `biid` or `eqid` instance.

We can also use justified theorems for special instances of definition axioms that can be justified using fewer axioms than the full justified restatement. For instance, `df-sb` can be justified with fewer axioms under the hypothesis that `ph` is a tautology:

```
  ${
    $d x y $.  $d t y $.  $d ph y $.
    sbt.1 $e |- ph $.
    $( Justified instance of ~ df-sb for ` ph ` a theorem.  Lemma for ~ sbt .
       (Proof modification is discouraged.) $)
    sbtlem $p |- ( [ t / x ] ph <-> A. y ( y = t -> A. x ( x = y -> ph ) ) ) $=
      ( vz wsb weq wi wal wb df-sb a1i ax-gen 2th a1ii ) ABDGCDHZBCHZAIZBJZIZCJ
      ZKFDHZBFHZAIZBJZIZFJZUBKABCDLUHUBUGFUFUCUEBAUDEMNMNUACTQSBAREMNMNOP $.

    $( A substitution into a theorem yields a theorem.  [...] $)
    sbt $p |- [ t / x ] ph $=
      ( vy wsb weq wi wal a1i ax-gen sbtlem mpbir ) ABCFECGZBEGZAHZBIZHZEIREQNP
      BAODJKJKABECDLM $.
    $( $j usage 'sbt' avoids 'ax-4' 'ax-5' 'ax-6' 'ax-7'; $)
  $}
```

This can be used to minimize axiom dependencies.

## License

`justcheck` and its documentation and tests are marked [CC0 1.0 Universal](https://creativecommons.org/publicdomain/zero/1.0/); see `COPYING` for more information. The dependency `metamath-rs` is licensed MIT or Apache-2.0; see its [`LICENSE-APACHE`](https://github.com/metamath/metamath-knife/blob/v0.3.9/LICENSE-APACHE) and [`LICENSE-MIT`](https://github.com/metamath/metamath-knife/blob/v0.3.9/LICENSE-MIT) for more information.

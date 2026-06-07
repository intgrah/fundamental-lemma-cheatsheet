#import "lib.typ": *
#show: conf

#let (absurd, case, fst, inl, inr, rec, snd, succ, zero) = (
  "absurd",
  "case",
  "fst",
  "inl",
  "inr",
  "rec",
  "snd",
  "succ",
  "zero",
).map(math.sans)
#let ang(..xs) = $lr(chevron.l #xs.pos().join(math.comma) chevron.r)$

= Syntax
$
  sigma, tau & ::= 1 | 0 | NN | sigma -> tau | sigma times tau | sigma + tau \
           t & ::= x | lambda x:sigma. t | t med t | ang() | absurd t \
             & | ang(t, t) | fst t | snd t \
             & | inl t | inr t | case(t, inl x => t, inr y => t) \
             & | zero | succ t | rec(t, zero => t, succ x med r => t) \
           v & ::= lambda x:sigma. t | ang() | ang(v, v) \
             & | inl v | inr v | zero | succ v
$

= Typing
#masonry(
  pt(rule(name: [Var], $x:tau in Gamma$, $Gamma tack x : tau$)),
  pt(rule(name: [Abs], $Gamma, x:sigma tack t : tau$, $Gamma tack lambda x:sigma. t : sigma -> tau$)),
  pt(rule(name: [App], $Gamma tack t : sigma -> tau$, $Gamma tack s : sigma$, $Gamma tack t med s : tau$)),
  pt(rule(name: [$1$], $Gamma tack ang() : 1$)),
  pt(rule(name: [$0$], $Gamma tack t : 0$, $Gamma tack absurd t : tau$)),
  pt(rule(
    name: [Pair],
    $Gamma tack t : sigma$,
    $Gamma tack s : tau$,
    $Gamma tack ang(t, s) : sigma times tau$,
  )),
  pt(rule(name: [Fst], $Gamma tack t : sigma times tau$, $Gamma tack fst t : sigma$)),
  pt(rule(name: [Snd], $Gamma tack t : sigma times tau$, $Gamma tack snd t : tau$)),
  pt(rule(name: [Inl], $Gamma tack t : sigma$, $Gamma tack inl t : sigma + tau$)),
  pt(rule(name: [Inr], $Gamma tack t : tau$, $Gamma tack inr t : sigma + tau$)),
  pt(rule(
    name: [Case],
    $Gamma tack t : sigma + tau$,
    $Gamma, x:sigma tack u : rho$,
    $Gamma, y:tau tack w : rho$,
    $Gamma tack case(t, inl x => u, inr y => w) : rho$,
  )),
  pt(rule(name: [Zero], $Gamma tack zero : NN$)),
  pt(rule(name: [Succ], $Gamma tack t : NN$, $Gamma tack succ t : NN$)),
  pt(rule(
    name: [Rec],
    $Gamma tack t : NN$,
    $Gamma tack t_z : rho$,
    $Gamma, x:NN, r:rho tack t_s : rho$,
    $Gamma tack rec(t, zero => t_z, succ x med r => t_s) : rho$,
  )),
)

= Operational semantics
$
  E & ::= [dot.c] | E med t | v med E | ang(E, t) | ang(v, E) | fst E | snd E \
    & | inl E | inr E | case(E, ...) | succ E | rec(E, ...) | absurd E
$

#masonry(
  pt(rule($t ~> t'$, $E[t] ~> E[t']$)),
  pt(rule($(lambda x:sigma. t) med v ~> t[v \/ x]$)),
  pt(rule($fst ang(v, w) ~> v$)),
  pt(rule($snd ang(v, w) ~> w$)),
  pt(rule($case(inl v, inl x => u, inr y => w) ~> u[v \/ x]$)),
  pt(rule($case(inr v, inl x => u, inr y => w) ~> w[v \/ y]$)),
  pt(rule($rec(zero, zero => t_z, succ x med r => t_s) ~> t_z$)),
  pt(rule(
    $rec(succ v, zero => t_z, succ x med r => t_s) ~> t_s [v \/ x, rec(v, zero => t_z, succ x med r => t_s) \/ r]$,
  )),
)


= Logical relation
#[
  #let setR(cond) = ${ t mid(|) exists v. med t ~>^* v #cond }$
  $
                    R_1 & = #setR([]) \
                    R_0 & = emptyset \
                   R_NN & = #setR([]) \
       R_(sigma -> tau) & = #setR($and forall s in R_sigma. med v med s in R_tau$) \
    R_(sigma times tau) & = #setR($and fst v in R_sigma and snd v in R_tau$) \
        R_(sigma + tau) & = #setR($and (case(v, inl v' => v' in R_sigma, inr v' => v' in R_tau))$)
  $
]

#tagged([Closure], $ dot.c tack t : T and t ~>^* t' ==> (t in R_T <==> t' in R_T) $)

= Fundamental theorem
#[
  #let mk(n) = text(fill: rgb("#1457d6"), weight: "bold")[(#n)]

  #mk(1)~$Gamma = x_1:sigma_1, ..., x_n:sigma_n$ \
  #mk(2)~values $v_i in R_(sigma_i)$ for each $i$ \
  #mk(3)~$gamma = [v_1 \/ x_1, ..., v_n \/ x_n]$ \
  #mk(4)~$Gamma tack t : tau$ \
  $==>$ $gamma(t) in R_tau$. By induction on #mk(4).
]

#tagged([Termination], $ dot.c tack t : tau ==> t ~>^* v $)
#tagged([Consistency], $ ¬(dot.c tack t : 0) $)

*Case Var.*
#row(
  pt(rule(name: [Var], sh("a", $x_j : sigma_j in Gamma$), $Gamma tack x_j : sigma_j$)),
  pt(rule(sh("a", $x_j : sigma_j in Gamma$), $v_j in R_(sigma_j)$, $gamma(x_j) = v_j in R_(sigma_j)$)),
)

*Case Abs.*
#up(pt(rule(
  name: [Abs],
  sh("a", $Gamma, x:sigma tack t_2 : tau_2$),
  $Gamma tack lambda x:sigma. t_2 : sigma -> tau_2$,
)))
#dn[
  #pt(rule($s in R_sigma$, sh("i", $s ~>^* w$)))
  #pt(rule(
    rule(
      sh("i", $s ~>^* w$),
      $(lambda x:sigma. gamma(t_2)) med s ~>^* gamma(t_2)[w \/ x]$,
    ),
    rule(
      sh("a", $Gamma, x:sigma tack t_2 : tau_2$),
      rule($s in R_sigma$, sh("i", $s ~>^* w$), $w in R_sigma$),
      $gamma(t_2)[w \/ x] in R_(tau_2)$,
    ),
    $(lambda x:sigma. gamma(t_2)) med s in R_(tau_2)$,
  ))
]

*Case App.*
#up(pt(rule(
  name: [App],
  sh("a", $Gamma tack t_1 : sigma -> tau$),
  sh("b", $Gamma tack t_2 : sigma$),
  $Gamma tack t_1 med t_2 : tau$,
)))
#dn[
  #pt(rule(sh("a", $Gamma tack t_1 : sigma -> tau$), sh("i", $gamma(t_1) in R_(sigma->tau)$)))
  #pt(rule(
    rule(
      rule(sh("i", $gamma(t_1) in R_(sigma->tau)$), $gamma(t_1) ~>^* v_1$),
      $gamma(t_1) med gamma(t_2) ~>^* v_1 med gamma(t_2)$,
    ),
    rule(
      rule(sh("i", $gamma(t_1) in R_(sigma->tau)$), $forall s in R_sigma. med v_1 med s in R_tau$),
      rule(sh("b", $Gamma tack t_2 : sigma$), $gamma(t_2) in R_sigma$),
      $v_1 med gamma(t_2) in R_tau$,
    ),
    $gamma(t_1 med t_2) in R_tau$,
  ))
]

*Case Unit.*
#row(
  pt(rule(name: [Unit], $Gamma tack ang() : 1$)),
  pt(rule($ang() ~>^* ang()$, $ang() in R_1$)),
)

*Case Absurd.*
#row(
  pt(rule(name: [$0$], sh("a", $Gamma tack t : 0$), $Gamma tack absurd t : rho$)),
  pt(rule(
    rule(
      rule(sh("a", $Gamma tack t : 0$), $gamma(t) in R_0 = emptyset$),
      $bot$,
    ),
    $absurd gamma(t) in R_rho$,
  )),
)

*Case Pair.*
#up(pt(rule(
  name: [Pair],
  sh("a", $Gamma tack t_1 : sigma$),
  sh("b", $Gamma tack t_2 : tau$),
  $Gamma tack ang(t_1, t_2) : sigma times tau$,
)))
#dn[
  #grid(
    columns: (auto, auto),
    column-gutter: 3em,
    pt(rule(rule(sh("a", $Gamma tack t_1 : sigma$), sh("i", $gamma(t_1) in R_sigma$)), sh(
      "iii",
      $gamma(t_1) ~>^* v_1$,
    ))),
    pt(rule(rule(sh("b", $Gamma tack t_2 : tau$), sh("ii", $gamma(t_2) in R_tau$)), sh("iv", $gamma(t_2) ~>^* v_2$))),
  )
  #pt(rule(
    $fst ang(v_1, v_2) ~>^* v_1$,
    rule(sh("i", $gamma(t_1) in R_sigma$), sh("iii", $gamma(t_1) ~>^* v_1$), $v_1 in R_sigma$),
    $fst ang(v_1, v_2) in R_sigma$,
  ))
  #pt(rule(
    $snd ang(v_1, v_2) ~>^* v_2$,
    rule(sh("ii", $gamma(t_2) in R_tau$), sh("iv", $gamma(t_2) ~>^* v_2$), $v_2 in R_tau$),
    $snd ang(v_1, v_2) in R_tau$,
  ))
  #pt(rule(
    rule(
      sh("iii", $gamma(t_1) ~>^* v_1$),
      sh("iv", $gamma(t_2) ~>^* v_2$),
      $ang(gamma(t_1), gamma(t_2)) ~>^* ang(v_1, v_2)$,
    ),
    $fst ang(v_1, v_2) in R_sigma$,
    $snd ang(v_1, v_2) in R_tau$,
    $ang(gamma(t_1), gamma(t_2)) in R_(sigma times tau)$,
  ))
]

*Case Fst.*
#row(
  pt(rule(name: [Fst], sh("a", $Gamma tack t : sigma times tau$), $Gamma tack fst t : sigma$)),
  [
    #pt(rule(sh("a", $Gamma tack t : sigma times tau$), sh("i", $gamma(t) in R_(sigma times tau)$)))
    #pt(rule(
      rule(
        rule(sh("i", $gamma(t) in R_(sigma times tau)$), $gamma(t) ~>^* v$),
        $fst gamma(t) ~>^* fst v$,
      ),
      rule(sh("i", $gamma(t) in R_(sigma times tau)$), $fst v in R_sigma$),
      $fst gamma(t) in R_sigma$,
    ))
  ],
)

*Case Snd.*
#row(
  pt(rule(name: [Snd], sh("a", $Gamma tack t : sigma times tau$), $Gamma tack snd t : tau$)),
  [
    #pt(rule(sh("a", $Gamma tack t : sigma times tau$), sh("i", $gamma(t) in R_(sigma times tau)$)))
    #pt(rule(
      rule(
        rule(sh("i", $gamma(t) in R_(sigma times tau)$), $gamma(t) ~>^* v$),
        $snd gamma(t) ~>^* snd v$,
      ),
      rule(sh("i", $gamma(t) in R_(sigma times tau)$), $snd v in R_tau$),
      $snd gamma(t) in R_tau$,
    ))
  ],
)

*Case Inl.*
#row(
  pt(rule(name: [Inl], sh("a", $Gamma tack t : sigma$), $Gamma tack inl t : sigma + tau$)),
  [
    #pt(rule(rule(sh("a", $Gamma tack t : sigma$), sh("i", $gamma(t) in R_sigma$)), sh("ii", $gamma(t) ~>^* v'$)))
    #pt(rule(
      rule(
        sh("ii", $gamma(t) ~>^* v'$),
        $inl gamma(t) ~>^* inl v'$,
      ),
      rule(sh("i", $gamma(t) in R_sigma$), sh("ii", $gamma(t) ~>^* v'$), $v' in R_sigma$),
      $inl gamma(t) in R_(sigma+tau)$,
    ))
  ],
)

*Case Inr.*
#row(
  pt(rule(name: [Inr], sh("a", $Gamma tack t : tau$), $Gamma tack inr t : sigma + tau$)),
  [
    #pt(rule(rule(sh("a", $Gamma tack t : tau$), sh("i", $gamma(t) in R_tau$)), sh("ii", $gamma(t) ~>^* v'$)))
    #pt(rule(
      rule(
        sh("ii", $gamma(t) ~>^* v'$),
        $inr gamma(t) ~>^* inr v'$,
      ),
      rule(sh("i", $gamma(t) in R_tau$), sh("ii", $gamma(t) ~>^* v'$), $v' in R_tau$),
      $inr gamma(t) in R_(sigma+tau)$,
    ))
  ],
)

*Case Case* (inl branch). $K(z) = case(z, inl x => gamma(t_1), inr y => gamma(t_2))$.
#up(pt(rule(
  name: [Case],
  sh("a", $Gamma tack t_0 : sigma+tau$),
  sh("b", $Gamma, x:sigma tack t_1 : rho$),
  sh("c", $Gamma, y:tau tack t_2 : rho$),
  $Gamma tack K(t_0) : rho$,
)))
#dn[
  #pt(rule(sh("a", $Gamma tack t_0 : sigma+tau$), sh("i", $gamma(t_0) in R_(sigma+tau)$)))
  #pt(rule(
    rule(
      rule(sh("i", $gamma(t_0) in R_(sigma+tau)$), $gamma(t_0) ~>^* inl v'$),
      $K(gamma(t_0)) ~>^* gamma(t_1)[v' \/ x]$,
    ),
    rule(
      sh("b", $Gamma, x:sigma tack t_1 : rho$),
      rule(sh("i", $gamma(t_0) in R_(sigma+tau)$), $v' in R_sigma$),
      $gamma(t_1)[v' \/ x] in R_rho$,
    ),
    $K(gamma(t_0)) in R_rho$,
  ))
]

*Case Zero.*
#row(
  pt(rule(name: [Zero], $Gamma tack zero : NN$)),
  pt(rule($zero ~>^* zero$, $zero in R_NN$)),
)

*Case Succ.*
#row(
  pt(rule(name: [Succ], sh("a", $Gamma tack t : NN$), $Gamma tack succ t : NN$)),
  [
    #pt(rule(sh("a", $Gamma tack t : NN$), sh("i", $gamma(t) in R_NN$)))
    #pt(rule(
      rule(
        rule(sh("i", $gamma(t) in R_NN$), $gamma(t) ~>^* v'$),
        $succ gamma(t) ~>^* succ v'$,
      ),
      $succ gamma(t) in R_NN$,
    ))
  ],
)

*Case Rec.* $P(s) = rec(s, zero => gamma(t_z), succ x med r => gamma(t_s))$. Inner induction on the numeral $n$ that $gamma(t)$ reaches.
#up(pt(rule(
  name: [Rec],
  sh("c", $Gamma tack t : NN$),
  sh("a", $Gamma tack t_z : rho$),
  sh("b", $Gamma, x:NN, r:rho tack t_s : rho$),
  $Gamma tack P(t) : rho$,
)))
#dn[
  #pt(rule(
    $P(zero) ~>^* gamma(t_z)$,
    rule(sh("a", $Gamma tack t_z : rho$), $gamma(t_z) in R_rho$),
    $P(zero) in R_rho$,
  ))
  #pt(rule(
    $P(succ k) ~>^* gamma(t_s)[k \/ x, P(k) \/ r]$,
    rule(
      sh("b", $Gamma, x:NN, r:rho tack t_s : rho$),
      $k in R_NN$,
      box[#grey[(IH)]#h(0.3em)$P(k) in R_rho$],
      $gamma(t_s)[k \/ x, P(k) \/ r] in R_rho$,
    ),
    $P(succ k) in R_rho$,
  ))
  #pt(rule(
    rule(
      rule(sh("c", $Gamma tack t : NN$), $gamma(t) in R_NN$, $gamma(t) ~>^* n$),
      $P(gamma(t)) ~>^* P(n)$,
    ),
    $P(n) in R_rho$,
    $P(gamma(t)) in R_rho$,
  ))
]

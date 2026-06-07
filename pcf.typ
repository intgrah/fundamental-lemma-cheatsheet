#import "lib.typ": *
#show: conf

#let (nat, bool, succ, pred, fun, fix, tru, fls, isz, cond) = (
  "nat",
  "bool",
  "succ",
  "pred",
  "fun",
  "fix",
  "true",
  "false",
  "zero?",
  "if",
).map(math.sans)
#let ite(b, t, e) = $#math.sans("if") #b #math.sans("then") #t #math.sans("else") #e$
#let fa = $scripts(lt.tri)$
#let ev = $scripts(arrow.b.double)$
#let sem(t) = $bracket.l.stroked #t bracket.r.stroked$

= Syntax
$
  tau & ::= nat | bool | tau -> tau \
    t & ::= 0 | succ(t) | pred(t) | tru | fls | isz(t) | ite(t, t, t) \
      & | x | fun x:tau. t | t med t | fix(t) \
    v & ::= 0 | succ(v) | tru | fls | fun x:tau. t
$

= Typing
#masonry(
  pt(rule(name: [Zero], $Gamma tack 0 : nat$)),
  pt(rule(name: [Succ], $Gamma tack t : nat$, $Gamma tack succ(t) : nat$)),
  pt(rule(name: [Pred], $Gamma tack t : nat$, $Gamma tack pred(t) : nat$)),
  pt(rule(name: [Isz], $Gamma tack t : nat$, $Gamma tack isz(t) : bool$)),
  pt(rule(name: [True], $Gamma tack tru : bool$)),
  pt(rule(name: [False], $Gamma tack fls : bool$)),
  pt(rule(name: [Var], $Gamma(x) = tau$, $Gamma tack x : tau$)),
  pt(rule(name: [Fix], $Gamma tack f : tau -> tau$, $Gamma tack fix(f) : tau$)),
  pt(rule(name: [Fun], $Gamma, x:tau tack t : tau'$, $Gamma tack fun x:tau. t : tau -> tau'$)),
  pt(rule(name: [App], $Gamma tack f : tau -> tau'$, $Gamma tack u : tau$, $Gamma tack f med u : tau'$)),
  pt(rule(
    name: [If],
    $Gamma tack b : bool$,
    $Gamma tack t_1 : tau$,
    $Gamma tack t_2 : tau$,
    $Gamma tack ite(b, t_1, t_2) : tau$,
  )),
)

= Operational semantics
#masonry(
  pt(rule(name: [Val], $v ev v$)),
  pt(rule(name: [Succ], $t ev v$, $succ(t) ev succ(v)$)),
  pt(rule(name: [Pred], $t ev succ(v)$, $pred(t) ev v$)),
  pt(rule(name: [Isz-t], $t ev 0$, $isz(t) ev tru$)),
  pt(rule(name: [Isz-f], $t ev succ(v)$, $isz(t) ev fls$)),
  pt(rule(name: [Fix], $f med (fix(f)) ev v$, $fix(f) ev v$)),
  pt(rule(
    name: [If-t],
    $b ev tru$,
    $t_1 ev v$,
    $ite(b, t_1, t_2) ev v$,
  )),
  pt(rule(
    name: [If-f],
    $b ev fls$,
    $t_2 ev v$,
    $ite(b, t_1, t_2) ev v$,
  )),
  pt(rule(name: [App], $f ev fun x:tau. t$, $t[u slash x] ev v$, $f med u ev v$)),
)

= Denotational semantics
#masonry(
  $sem(nat) = NN_bot$,
  $sem(bool) = BB_bot$,
  $sem(tau -> tau') = [sem(tau) -> sem(tau')]$,
  $sem(x) rho = rho(x)$,
  $sem(t_1 med t_2) rho = sem(t_1) rho (sem(t_2) rho)$,
  $sem(fun x:tau. t) rho = lambda d in sem(tau). med sem(t) (rho[x arrow.r.bar d])$,
  $sem(0) rho = 0$,
  $sem(succ(t)) rho = succ_bot (sem(t) rho)$,
  $sem(pred(t)) rho = pred_bot (sem(t) rho)$,
  $sem(isz(t)) rho = isz_bot (sem(t) rho)$,
  $sem(ite(b, t_1, t_2)) rho = cond(sem(b) rho, sem(t_1) rho, sem(t_2) rho)$,
  $sem(fix(f)) rho = fix(sem(f) rho) = union.sq.big_(n >= 0) (sem(f) rho)^n (bot)$,
)

= Formal approximation
$
            d fa_nat t & <==> (d in NN ==> t ev d) \
           d fa_bool t & <==> (d in BB ==> t ev d) \
  d fa_(tau -> tau') t & <==> (forall e, u. e fa_tau u ==> d(e) fa_(tau') t med u)
$

#tagged($bot$, $ bot fa_tau t $)
#tagged([chain-closed], $ { d mid(|) d fa_tau t } "is chain-closed in" sem(tau) $)
#tagged([closure], $ (forall v. med t ev v ==> t' ev v) and d fa_tau t ==> d fa_tau t' $)

= Fundamental property
#[
  #let mk(n) = text(fill: rgb("#1457d6"), weight: "bold")[(#n)]

  #mk(1)~$Gamma = x_1:tau_1, dots, x_n:tau_n$; #h(0.4em) environment $rho$, substitution $sigma$ \
  #mk(2)~$rho(x_i) fa_(tau_i) sigma(x_i)$ for each $i$ \
  #mk(3)~$Gamma tack t : tau$ \
  $==>$ $sem(t) rho fa_tau t[sigma]$. By induction on #mk(3). Then adequacy: closed $t$, ground value $v$, $sem(t) = floor.l v floor.r ==> sem(t) fa t ==> t ev v$.
]

*Case Var.*
#row(
  pt(rule(name: [Var], sh("a", $Gamma(x_j) = tau_j$), $Gamma tack x_j : tau_j$)),
  pt(rule(
    sh("a", $rho(x_j) fa_(tau_j) sigma(x_j)$),
    $sem(x_j) rho = rho(x_j) fa_(tau_j) sigma(x_j) = x_j[sigma]$,
  )),
)

*Case App.*
#row(
  pt(rule(
    name: [App],
    sh("a", $Gamma tack f : tau -> tau'$),
    sh("b", $Gamma tack u : tau$),
    $Gamma tack f med u : tau'$,
  )),
  pt(rule(
    rule(sh("a", $Gamma tack f : tau -> tau'$), $sem(f) rho fa_(tau -> tau') f[sigma]$),
    rule(sh("b", $Gamma tack u : tau$), $sem(u) rho fa_tau u[sigma]$),
    $sem(f med u) rho fa_(tau') (f med u)[sigma]$,
  )),
)

*Case Fun.* For arbitrary $e fa_tau u$.
#up(pt(rule(name: [Fun], sh("a", $Gamma, x:tau tack t : tau'$), $Gamma tack fun x:tau. t : tau -> tau'$)))
#dn(pt(rule(
  rule(
    rule(
      sh("a", $Gamma, x:tau tack t : tau'$),
      $e fa_tau u$,
      $sem(t) (rho[x arrow.r.bar e]) fa_(tau') t[sigma][u slash x]$,
    ),
    $(fun x:tau. t[sigma]) med u ev v #h(0.4em) <== #h(0.4em) t[sigma][u slash x] ev v$,
    $sem(t) (rho[x arrow.r.bar e]) fa_(tau') (fun x:tau. t[sigma]) med u$,
  ),
  $sem(fun x:tau. t) rho fa_(tau -> tau') fun x:tau. t[sigma]$,
)))

*Case Zero.*
#row(
  pt(rule(name: [Zero], $Gamma tack 0 : nat$)),
  pt(rule($0 ev 0$, $sem(0) rho = 0 fa_nat 0$)),
)

*Case True.*
#row(
  pt(rule(name: [True], $Gamma tack tru : bool$)),
  pt(rule($tru ev tru$, $sem(tru) rho = tru fa_bool tru$)),
)

*Case False.*
#row(
  pt(rule(name: [False], $Gamma tack fls : bool$)),
  pt(rule($fls ev fls$, $sem(fls) rho = fls fa_bool fls$)),
)

*Case Succ.*
#row(
  pt(rule(name: [Succ], sh("a", $Gamma tack t : nat$), $Gamma tack succ(t) : nat$)),
  pt(rule(
    rule(sh("a", $Gamma tack t : nat$), $sem(t) rho fa_nat t[sigma]$),
    $t[sigma] ev n ==> succ(t[sigma]) ev succ(n)$,
    $succ_bot (sem(t) rho) fa_nat succ(t[sigma])$,
  )),
)

*Case Pred.*
#row(
  pt(rule(name: [Pred], sh("a", $Gamma tack t : nat$), $Gamma tack pred(t) : nat$)),
  pt(rule(
    rule(sh("a", $Gamma tack t : nat$), $sem(t) rho fa_nat t[sigma]$),
    $t[sigma] ev succ(n) ==> pred(t[sigma]) ev n$,
    $pred_bot (sem(t) rho) fa_nat pred(t[sigma])$,
  )),
)

*Case Zero?.*
#row(
  pt(rule(name: [Isz], sh("a", $Gamma tack t : nat$), $Gamma tack isz(t) : bool$)),
  pt(rule(
    rule(sh("a", $Gamma tack t : nat$), $sem(t) rho fa_nat t[sigma]$),
    $t[sigma] ev 0 ==> isz(t[sigma]) ev tru$,
    $isz_bot (sem(t) rho) fa_bool isz(t[sigma])$,
  )),
)

*Case If* ($sem(b) rho = tru$ branch; $fls$ symmetric).
#up(pt(rule(
  name: [If],
  sh("a", $Gamma tack b : bool$),
  sh("b", $Gamma tack t_1 : tau$),
  sh("c", $Gamma tack t_2 : tau$),
  $Gamma tack ite(b, t_1, t_2) : tau$,
)))
#dn(pt(rule(
  rule(sh("b", $Gamma tack t_1 : tau$), $sem(t_1) rho fa_tau t_1[sigma]$),
  rule(
    rule(sh("a", $Gamma tack b : bool$), $sem(b) rho fa_bool b[sigma]$, $b[sigma] ev tru$),
    $ite(b[sigma], t_1[sigma], t_2[sigma]) ev v #h(0.4em) <== #h(0.4em) t_1[sigma] ev v$,
  ),
  $cond(sem(b) rho, sem(t_1) rho, sem(t_2) rho) fa_tau ite(b[sigma], t_1[sigma], t_2[sigma])$,
)))

*Case Fix.* Scott induction on $S = { e mid(|) e fa_tau fix(f[sigma]) }$.
#up(pt(rule(name: [Fix], sh("a", $Gamma tack f : tau -> tau$), $Gamma tack fix(f) : tau$)))
#dn[
  #pt(rule(sh("⊥◁", $bot fa_tau fix(f[sigma])$)))
  #pt(rule(
    rule(
      rule(sh("a", $Gamma tack f : tau -> tau$), $sem(f) rho fa_(tau -> tau) f[sigma]$),
      box[#grey[(IH)]#h(0.3em)$e fa_tau fix(f[sigma])$],
      $sem(f) rho (e) fa_tau f[sigma] med (fix(f[sigma]))$,
    ),
    $fix(f[sigma]) ev v #h(0.4em) <== #h(0.4em) f[sigma] med (fix(f[sigma])) ev v$,
    $sem(f) rho (e) fa_tau fix(f[sigma])$,
  ))
  #pt(rule(
    sh("base", $bot fa_tau fix(f[sigma])$),
    sh("step", $sem(f) rho (e) fa_tau fix(f[sigma])$),
    sh("adm", [${ e mid(|) e fa_tau fix(f[sigma]) }$ chain-closed]),
    $sem(fix(f)) rho = union.sq.big_n (sem(f) rho)^n (bot) fa_tau fix(f[sigma])$,
  ))
]

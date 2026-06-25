#import "@preview/curryst:0.6.0": prooftree as pt, rule

#let grey(body) = text(fill: luma(140), body)
#let sh(c, body) = box[#grey[(#c)]#h(0.3em)#body]
#let masonry(..items) = align(center, {
  set par(leading: 2em)
  items.pos().map(box).join(h(2em))
})
#let palette = (
  up: (rgb("#fce8e6"), rgb("#c0392b")),
  dn: (rgb("#e6f4e6"), rgb("#2f8f3e")),
)
#let skin(kind) = {
  let (bg, fg) = palette.at(kind)
  (fill: bg, stroke: (left: 2pt + fg), inset: (x: 7pt, y: 5pt))
}
#let panel(kind, body) = block(..skin(kind), width: 100%, radius: 2pt, align(center, body))
#let up(body) = panel("up", body)
#let dn(body) = panel("dn", body)
#let row(a, b) = context {
  let cell(kind, body) = grid.cell(..skin(kind), align: center + horizon, body)
  let wa = measure(a).width.pt()
  let wb = measure(b).width.pt()
  grid(
    columns: (wa * 1fr, wb * 1fr),
    column-gutter: 0.8em,
    cell("up", a),
    cell("dn", b),
  )
}
#let tagged(name, body) = math.equation(block: true, numbering: _ => [(#name)], body)

#let conf(body) = {
  show heading: it => block(
    above: 1.4em,
    below: 0.5em,
    text(weight: "bold", size: 1em, it.body),
  )
  
  body
}

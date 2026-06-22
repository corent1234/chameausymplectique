  #let TODO(term) = {
  text(lime, box[✨ #term ✨])
}

#let form(num) = "../"+str(num)+"/corps.typ"
//Affichage de base
#let author = [Corentin Cornou]

#set text(lang: "fr")

#let conf(doc,title) = {
  set page(
  paper: "a4",
 header: align(right)[
    #title
  ],
  numbering: "1",
  margin: (
    bottom: 2cm,
    x: 2.5cm,
)
)
  set par(justify: true, first-line-indent: 7pt, linebreaks: "optimized")
  set text(
    font: "Luciole",
    size: 12pt,
  )
  // Heading show rules.
  columns(1, doc)
}

#let afficherTitre(title) =[
#align(center, text(17pt)[
  *#title*
])
#align(center, text(13pt)[
  #author])]

  
//Environnements pour les exos etc.
#import "@preview/ctheorems:1.1.3": *
#let theorem = thmbox("theorem", "Theorème", fill: rgb("#eeffee"))
#let proposition = thmbox("theorem", "Proposition", fill: rgb("#eeffee"))
#let lemma = thmbox("theorem", "Lemme", fill: rgb("#eeffee"))

#let corollary = thmplain(
  "corollaire",
  "Corollaire",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Définition", inset: (x: 1.2em, top: 1em))

#let propdef = thmbox("proposition-definition", "Proposition-Définition", inset: (x: 1.2em, top: 1em))

#let remark = thmbox("remarque", "Remarque", inset: (x: 1.2em, top: 1em))

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Preuve")

#let exo = thmplain("exercice", "Exercice")
#let rappel = thmplain("rappel", "Rappel")

#let cor = thmbox("correction", "Correction", fill:rgb("#eeffee"))

#let numbered_eq(content) = math.equation(
    block: true,
    numbering: "(1)",
    supplement:none,
    content,
)

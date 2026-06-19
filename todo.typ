// Gestion des différents todo
#import "@preview/drafting:0.2.2": margin-note, set-page-properties, note-outline, inline-note

#let legende(title : "Légende", list_of_todos_types) = grid(
  row-gutter: 10pt,
  heading(title),
  ..list_of_todos_types.values().map(todo_type => grid(
        columns: (1em, 1fr, 10pt),
        column-gutter: 5pt,
        align: (top, bottom, bottom),
        box(
          stroke: todo_type.stroke,
          width: 1em - 2pt,
          height: 1em - 2pt,
        ),
        [#todo_type.body #box(width: 1fr, repeat[.])],
      
    )
  )
)
#let todo_type(stroke,body) = (stroke:stroke, body:body)
#let todo_types = (
  todo :todo_type(red,"Todo général"),
  y:todo_type(yellow,"Fait obscur"),
  proof:todo_type(green,"À prouver"),
  source:todo_type(aqua,"À sourcer"),
  link:todo_type(fuchsia,"À lier dans le document"),
  draw:todo_type(purple,"À dessiner"),
)


#let todo(arg) = margin-note(stroke:todo_types.todo.stroke)[#arg]
#let toprove(arg)= margin-note(stroke:todo_types.proof.stroke)[#arg]
#let tolink(arg) = margin-note(stroke:todo_types.link.stroke)[#arg]
#let tosource(arg) = margin-note(stroke:todo_types.source.stroke)[#arg]
#let todraw(arg) = margin-note(stroke:todo_types.draw.stroke)[#arg]
#let y = margin-note(stroke:todo_types.y.stroke)[Pourquoi ?]



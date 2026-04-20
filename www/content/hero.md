# talktalk is a small, fully-typed language that kind of looks like Swift or Rust or Go ~~if you squint~~.

It wants to feel familiar and cozy, but still have the stuff that the college folk write about in their latex pdfs: type inference, sum types, protocols, algebraic effects, you know, that kind of stuff. 

It's mostly a way for me to understand compilers. You shouldn't use talktalk. But you might enjoy perusing it.

```tlk
// hello.tlk — a little tour
struct Owl {
  let name: String
  let greeting: String

  func hoot() {
    print(self.greeting + ", i'm " + self.name)
  }
}

let hoo = Owl(name: "hoo", greeting: "hi 🦉")
hoo.hoot()
```

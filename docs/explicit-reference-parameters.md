Lets add the concept of mutability to our system. I want the syntax to work like rust's:

```tlk
let foo = "hello" // foo is immutable
foo.append("sup") // should fail

let mut bar = "hello" // bar is mutable
bar.append("sup") // should work
```

We'll need to track mutability of properties:

```tlk
struct Person {
    let mut age: Int
    let bday: Int
}

Person(age: 123, bday: 12345678)

person.age = 456 // This works because age is mutable
person.bday = 456 // This is an error because bday is immutable
```

We'll need to track mutability of methods:

```tlk
struct Person {
    let mut age: Int
    let bday: Int

    init(age: Int, bday: Int) {
        self.age = age
        self.bday = bday // We can always set any property inside of an init
    }

    mut func changeAge(newAge: Int) {
        self.age = newAge // Works
    }

    func changeAgeNope(newAge: Int) {
        self.age = newAge // Error because the method isn't defined as mut
    }

    mut func changeBdayNope(newBday: Int) {
        self.bday = newBday // Error because bday isn't mutable
    }
}

Person(age: 123, bday: 12345678)

person.age = 456 // Works because age is mutable
person.bday = 456 // Error because bday is immutable
```

We'll also need to track mutability of params/args:

```tlk
func increment(mut x: Int) {
    x = x + 1
}

let mut y = 123
let z = 123

increment(x: y) // Works because y is mutable
increment(x: z) // Error because z is not mutable
```
/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.function
import Mathlib.Lean3Lib.init.data.option.basic
import Mathlib.Lean3Lib.init.util
import Mathlib.Lean3Lib.init.meta.tactic
import Mathlib.Lean3Lib.init.meta.mk_dec_eq_instance
import Mathlib.Lean3Lib.init.meta.json
 

universes l 

namespace Mathlib

/-! A component is a piece of UI which may contain internal state. Use component.mk to build new components.

## Using widgets.

To make a widget, you need to make a custom executor object and then instead of calling `save_info_thunk` you call `save_widget`.

Additionally, you will need a compatible build of the vscode extension or web app to use widgets in vscode.

## How it works:

The design is inspired by React.
If you are familiar with using React or Elm or a similar functional UI framework then that's helpful for this.
The [React article on reconciliation](https://reactjs.org/docs/reconciliation.html) might be helpful.

One can imagine making a UI for a particular object as just being a function `f : α → UI` where `UI` is some inductive datatype for buttons, textboxes, lists and so on.
The process of evaluating `f` is called __rendering__.
So for example `α` could be `tactic_state` and the function renders a goal view.

## HTML

For our purposes, `UI` is an HTML tree and is written `html α : Type`. I'm going to assume some familiarity with HTML for the purposes of this document.
An HTML tree is composed of elements and strings.
Each element has a tag such as "div", "span", "article" and so on and a set of attributes and child html.
Use the helper function `h : string → list (attr α) → list (html α) → html α` to build new pieces of `html`. So for example:

```lean
h "ul" [] [
     h "li" [] ["this is list item 1"],
     h "li" [style [("color", "blue")]] ["this is list item 2"],
     h "hr" [] [],
     h "li" [] [
          h "span" [] ["there is a button here"],
          h "button" [on_click (λ _, 3)] ["click me!"]
     ]
]
```
Has the type `html nat`.
The `nat` type is called the __action__ and whenever the user interacts with the UI, the html will emit an object of type `nat`.
So for example if the user clicks the button above, the html will 'emit' `3`.
The above example is compiled to the following piece of html:

```html
<ul>
  <li>this is list item 1</li>
  <li style="{ color: blue; }">this is list item 2</li>
  <hr/>
  <li>
     <span>There is a button here</span>
     <button onClick="[handler]">click me!</button>
  </li>
</ul>
```

## Components

In order for the UI to react to events, you need to be able to take these actions α and alter some state.
To do this we use __components__. `component` takes two type arguments: `π` and `α`. `α` is called the 'action' and `π` are the 'props'.
The props can be thought of as a kind of wrapped function domain for `component`. So given `C : component nat α`, one can turn this into html with
`html.of_component 4 C : html α`.

The base constructor for a component is `pure`:
```lean
meta def Hello : component string α := component.pure (λ s, ["hello, ", s, ", good day!"])

#html Hello "lean" -- renders "hello, lean, good day!"
```
So here a pure component is just a simple function `π → list (html α)`.
However, one can augment components with __hooks__.
The hooks available for compoenents are listed in the inductive definition for component.

Here we will just look at the `with_state` hook, which can be used to build components with inner state.

```
meta inductive my_action
| increment
| decrement
open my_action

meta def Counter : component unit α :=
component.with_state
     my_action          -- the action of the inner component
     int                -- the state
     (λ _, 0)           -- initialise the state
     (λ _ _ s, s)       -- update the state if the props change
     (λ _ s a,          -- update the state if an action was received
          match a with
          | increment := (s + 1, none) -- replace `none` with `some _` to emit an action
          | decrement := (s - 1, none)
          end
     )
$ component.pure (λ ⟨state, ⟨⟩⟩, [
     button "+" (λ _, increment),
     to_string state,
     button "-" (λ _, decrement)
  ])

#html Counter ()
```

You can add many hooks to a component.

- `filter_map_action` lets you filter or map actions that are emmitted by the component
- `map_props` lets you map the props.
- `with_should_update` will not re-render the child component if the given test returns false. This can be useful for efficiency.
- `with_state` discussed above.`
- `with_mouse` subscribes the component to the mouse state, for example whether or not the mouse is over the component. See the `tests/lean/widget/widget_mouse.lean` test for an example.

Given an active document, Lean (in server mode) maintains a set of __widgets__ for the document.
A widget is a component `c`, some `p : Props` and an internal state-manager which manages the states
of the component and subcomponents and also handles the routing of events from the UI.

## Reconciliation

If a parent component's state changes, this can cause child components to change position or to appear and dissappear.
However we want to preserve the state of these child components where we can.
The UI system will try to match up these child components through a process called __reconciliation__.

Reconciliation will make sure that the states are carried over correctly and will also not rerender subcomponents if they haven't changed their props or state.
To compute whether two components are the same, the system will perform a hash on their VM objects.
Not all VM objects can be hashed, so it's important to make sure that any items that you expect to change over the lifetime of the component are fed through the 'Props' argument.
This is why we need the props argument on `component`.
The reconciliation engine uses the `props_eq` predicate passed to the component constructor to determine whether the props have changed and hence whether the component should be re-rendered.

## Keys

If you have some list of components and the list changes according to some state, it is important to add keys to the components so
that if two components change order in the list their states are preserved.
If you don't provide keys or there are duplicate keys then you may get some strange behaviour in both the Lean widget engine and react.

It is possible to use incorrect HTML tags and attributes, there is (currently) no type checking that the result is a valid piece of HTML.
So for example, the client widget system will error if you add a `text_change_event` attribute to anything other than an element tagged with `input`.

## Styles with Tachyons

The widget system assumes that a stylesheet called 'tachyons' is present.
You can find documentation for this stylesheet at [Tachyons.io](http://tachyons.io/).
Tachyons was chosen because it is very terse and allows arbitrary styling without using inline styles and without needing to dynamically load a stylesheet.

## Further work (up for grabs!)

- Add type checking for html.
- Better error handling when the html tree is malformed.
- Better error handling when keys are malformed.
- Add a 'with_task' which lets long-running operations (eg running `simp`) not block the UI update.
- Timers, animation (ambitious).
- More event handlers
- Drag and drop support.
- The current perf bottleneck is sending the full UI across to the server for every update.
  Instead, it should be possible to send a smaller [JSON Patch](http://jsonpatch.com).
  Which is already supported by `json.hpp` and javascript ecosystem.

-/

namespace widget


inductive mouse_event_kind 
where
| on_click : mouse_event_kind
| on_mouse_enter : mouse_event_kind
| on_mouse_leave : mouse_event_kind


open Js_of_ocaml

let _ =
  Js.export "analyser"
    (object%js
           method analyse str = Main.run_simple (Js.to_string str)
           method main cmd = Main.main (List.map Js.to_string (Array.to_list (Js.to_array cmd)))
     end)

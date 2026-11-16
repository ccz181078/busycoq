let () =
let args =
Array.to_list Sys.argv |> List.tl
in
Inductive.exec args


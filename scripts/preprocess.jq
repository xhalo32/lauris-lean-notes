split("(^|\\n)(-/|/-)[[:space:]]*($|\\n)"; "") | 

(.[1] | split("\n")) as $lines | 
$lines[0] as $title |
($lines[1:] | join("\n")) as $metadata | 
.[2] as $preamble | 

"import Infra.Preamble",
$preamble,
"#doc (Manual) \"" + $title + "\" =>",
$metadata,
"```lean -show",
"namespace " + $ns,
"```",
(.[3:] | to_entries[] | select(.value | test("\\S")) |
    if (.key % 2) == 0
    then .value
    else "```lean\n" + .value + "\n```"
    end
)

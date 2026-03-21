lake init Document math

sed -i '/^weak\.linter\.mathlibStandardSet = true$/d' \
    lakefile.toml
echo '
[[lean_lib]]
name = "Infra"

[[lean_exe]]
name = "doc"
root = "Infra.Main"

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"' \
    >>lakefile.toml
set revline (grep "rev = " <lakefile.toml) 
echo $revline >>lakefile.toml

lake update

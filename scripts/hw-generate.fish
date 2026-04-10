set indir Examples
set outdir _out

if test -e _local/config.fish
    source _local/config.fish
end

set hwdir (path resolve $outdir/hw)
set srcdir (pwd)

mkdir -p $hwdir
pushd $indir
for file in *.lean
    echo "Processing $file"

    echo "\
/-
Exercises
---------

Fill in the parts labeled with __TODO__.

-/" > $hwdir/$file
    awk -f $srcdir/scripts/hw-process.awk <$file \
    | awk -f $srcdir/scripts/hw-process-blank.awk \
    >>$hwdir/$file
end
popd
set indir Document
set outdir _out

if test -e _local/config.fish
    source _local/config.fish
end
 
set docdir (path resolve $outdir/$indir)
set doc (path resolve $outdir/Document.lean)
set srcdir (pwd)


if not test -e $outdir
    echo "Init: $outdir"

    mkdir -p $outdir
    pushd $outdir
    fish $srcdir/scripts/init.fish
    popd
end

cp -rfv verso/* $outdir

rm -f $doc
rm -rf $docdir
mkdir -p $docdir

pushd $indir
for file in *.lean
    echo "Preprocessing $file"

    set name (path basename --no-extension $file)
    jq -Rsr \
        -f $srcdir/scripts/preprocess.jq \
        <$file >$docdir/$file
    echo "import $indir.$name" >>$doc    
end
popd 

echo 'import Infra.Preamble' >>$doc
cat Document.md >>$doc

cd $outdir 
rm -rf _out 
lake exe doc || return 1

cd _out/html-multi
cp -rfv $srcdir/assets/* .
cp -rfv $srcdir/custom/* .

for file in (find . -type f -name "index.html")
    echo "Postprocessing $file"

    python $srcdir/scripts/postprocess.py \
        <$file >"$file"_pp
    mv "$file"_pp $file
end

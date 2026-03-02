set tmpdir (mktemp -d)
pushd $tmpdir
mkdir -p woff2

curl -L -O https://www.gust.org.pl/projects/e-foundry/latin-modern/download/lm2.006otf.zip 
unzip lm2.006otf.zip

# Serif (Latin Modern Roman)
fonttools ttLib.woff2 compress lmroman10-regular.otf
mv lmroman10-regular.woff2 woff2/lm-roman-regular.woff2

fonttools ttLib.woff2 compress lmroman10-italic.otf
mv lmroman10-italic.woff2 woff2/lm-roman-italic.woff2

fonttools ttLib.woff2 compress lmroman10-bold.otf
mv lmroman10-bold.woff2 woff2/lm-roman-bold.woff2

fonttools ttLib.woff2 compress lmroman10-bolditalic.otf
mv lmroman10-bolditalic.woff2 woff2/lm-roman-bolditalic.woff2

# Sans (Latin Modern Sans)
fonttools ttLib.woff2 compress lmsans10-regular.otf
mv lmsans10-regular.woff2 woff2/lm-sans-regular.woff2

fonttools ttLib.woff2 compress lmsans10-bold.otf
mv lmsans10-bold.woff2 woff2/lm-sans-bold.woff2

cd woff2

set url https://cdn.jsdelivr.net/gh/cormullion/juliamono/webfonts/JuliaMono

curl -L -O $url-Regular.woff2
curl -L -O $url-RegularItalic.woff2
curl -L -O $url-Bold.woff2

popd

echo "
Downloaded fonts can be copied to assets with
mkdir -p assets/fonts
cp $tmpdir/woff2/*.woff2 assets/fonts
"
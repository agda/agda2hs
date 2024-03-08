#!/bin/zsh

# PREREQUISITES:
#   - generated target files are placed under build/
BUILD_DIR=build
#   - Agda generated HTML is placed under html/
AGDA_HTML_DIR=html

echo "Rendering translations..."
for f in $BUILD_DIR/**/**.*; do
  echo " *** file: $f ***"
  ext=${f##*.}
  fn=${${f#"$BUILD_DIR"/}%."$ext"}

  failMod=$(case $ext in
    "err") echo 'Fail.';;
    *) echo '';;
  esac)

  sourceHtml=$AGDA_HTML_DIR/"$failMod"$(echo $fn | tr '/' '.').html
  [ ! -f $sourceHtml ] && \
    echo " No corresponding HTML for $f (should be at $sourceHtml)" && \
    exit 1
  echo " $f ~ $sourceHtml"

  mdFn=$BUILD_DIR/"$fn".md
  echo " Generating $mdFn"
  mdBlock=$(case $ext in
    "hs") echo "haskell";;
    "rs") echo "rust";;
    "agda") echo "agda";;
    "sh") echo "bash";;
    "js") echo "javascript";;
    *) echo "";;
  esac)
  echo "\`\`\`$mdBlock" > $mdFn
  cat $f >> $mdFn
  echo "\`\`\`" >> $mdFn

  targetHtml=$BUILD_DIR/"$fn".html
  echo " Generating $targetHtml"
  pandoc --quiet -i "$mdFn" -o "$targetHtml" -s --highlight-style=tango
  mkdir -p "$AGDA_HTML_DIR/$BUILD_DIR"
  echo " Copy build/ into html/"
  cp -r $BUILD_DIR/ $AGDA_HTML_DIR/

  echo " Modifying $sourceHtml"
  sed -i "s%class=\"Agda\"%class=\"split left Agda\"%g" $sourceHtml
  sed -i "s%</body>%<div class=\"split right\"><embed src=\"$targetHtml\"/></div></body>%g" $sourceHtml
done
echo "...done!"

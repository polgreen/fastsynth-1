for f in *.sl; do
echo $f
timeout 300 time fastsynth --arrays $f > $f.output
done
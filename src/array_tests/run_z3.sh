for f in horn*.smt2; do
echo $f
timeout 60 z3 $f 
done
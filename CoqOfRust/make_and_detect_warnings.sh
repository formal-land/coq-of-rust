# The coqc_logs.txt won't be removed, as this could be a good source of log

echo "Executing make..."
make |& tee -a coqc_logs.txt

# Ignore lines produced by make
# IGNORE_IDENTIFIER="COQC"

WARNING_IDENTIFIER="Warning"

echo "Checking if there are warnings in output..."

while read -r line
do
  if [[ $line == $WARNING_IDENTIFIER* ]]
  then
    echo "Warning detected in output"
    echo $line
    exit 1
  else
    continue
  fi
done <coqc_logs.txt

echo "Checking complete"

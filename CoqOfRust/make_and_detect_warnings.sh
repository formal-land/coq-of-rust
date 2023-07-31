# The stderr_warnings.txt won't be removed, as this could be a good source of log
echo "Creating error file..."
> stderr_warnings.txt

echo "Executing make..."
make |& tee -a stderr_warnings.txt

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
done <stderr_warnings.txt

echo "Checking complete"

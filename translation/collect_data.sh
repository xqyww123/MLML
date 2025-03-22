#!/bin/bash

#SBATCH --partition=standard
#SBATCH --mem=250G
#SBATCH --nodes=1

#SBATCH --cpus-per-task=108
#SBATCH --time=400:00:00

#SBATCH --job-name=MiniLang_DataGen
#SBATCH --output=logs/top.%j.stdout
#SBATCH --error=logs/top.%j.stderr

PATH=./contrib/Isabelle2024/bin:$PATH

total_parts=$(( $2 * 2))
iii=$1

pkill -f 'repl_server_watch_dog\.sh'
pkill -f 'translator_watch_dog\.sh'
pkill -f 'repl_server\.sh'
pkill -f 'Isabelle2024/heaps/polyml'

if command -v nproc >/dev/null 2>&1; then
    all_proc=$(nproc)
elif [[ "$OSTYPE" == "darwin"* ]]; then
    all_proc=$(sysctl -n hw.ncpu)
else
    all_proc=$(grep -c ^processor /proc/cpuinfo)
fi
num_processors=$(( $all_proc / 2 ))



###### Worker 1 ###########

i=$(($iii * 2))
mkdir -p ./cache/translation/repl_tmps/$i

port="6$(printf "%03d" $i)"
repl_temp_dir="$(realpath ./cache/translation/repl_tmps/$i)"
./Isa-REPL/repl_server_watch_dog.sh 127.0.0.1:$port HOL $repl_temp_dir -o threads=$num_processors -o timeout_scale=1 &
repl_pid=$!

sleep 4
./Isa-Proof-Shell/translator_watch_dog.sh 127.0.0.1:$port ./translation/results/minilang.$i.db ./translation/tasks/targets.$i &
translator_pid=$!


###### Worker 2 ###########

i=$(($iii * 2 + 1))
mkdir -p ./cache/translation/repl_tmps/$i

port="6$(printf "%03d" $i)"
repl_temp_dir="$(realpath ./cache/translation/repl_tmps/$i)"
./Isa-REPL/repl_server_watch_dog.sh 127.0.0.1:$port HOL $repl_temp_dir -o threads=$num_processors -o timeout_scale=1 &
repl_pid2=$!


sleep 4
./Isa-Proof-Shell/translator_watch_dog.sh 127.0.0.1:$port ./translation/results/minilang.$i.db ./translation/tasks/targets.$i &
translator_pid2=$!


######### Epilogue #########

cleanup() {
  kill $repl_pid 2>/dev/null
  kill $repl_pid2 2>/dev/null
  pkill -f 'repl_server_watch_dog\.sh'
  pkill -f 'translator_watch_dog\.sh'
  pkill -f 'repl_server\.sh'
  pkill -f 'Isabelle2024/heaps/polyml'
  exit
}
trap cleanup EXIT SIGINT SIGTERM SIGHUP SIGQUIT

wait $translator_pid
wait $translator_pid2
kill $repl_pid
kill $repl_pid2

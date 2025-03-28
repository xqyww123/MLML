#! /bin/bash
echo "This is a development tool used to test the error-rescue mechanism when a server is offline."

if [ "$EUID" -ne 0 ]; then
    echo "This script must be run as root"
    exit 1
fi
echo "Blocking server on port 6666"
iptables -A INPUT -p tcp --dport 6666 -j DROP 
iptables -A OUTPUT -p tcp --sport 6666 -j DROP
read -rsp "Press any key to unblock..." -n 1 key
iptables -D INPUT -p tcp --dport 6666 -j DROP 
iptables -D OUTPUT -p tcp --sport 6666 -j DROP
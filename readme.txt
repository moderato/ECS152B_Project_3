This p2pim program can discover users in the local area network by sending UDP broadcast messages, and connecting and chatting with connected users using TCP messaging. Besides it can request user list from the user, and send local user list to users who are requesting it. The local user list is maintained by using a linked list. When a trust anchor is presented, it can perform encrypted communication with authenticated peers. When the trust anchor is not found, it can still unencryptedly communicate with peers.

As the system getopt_long function is used to process the command argument, the grammar of the command is a little bit different from the requirement. If you are specifying the username, please use '-u' as given. Otherwise please add a '-' before each flag, e.g. use '--up' instead of '-up'. Unfortunately the '-pp' option is not implemented due to limited time. 

This program is a text-based program using non-canonical mode. When the program is running, feel free to press 'h' for help information.

To install the server, run "make" in the terminal.
To uninstall the server, run "make clean" in the terminal.

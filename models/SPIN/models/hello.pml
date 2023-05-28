/* PROPERTIES */
ltl p1 { <> p }
ltl p2 { [] p }

/* MODEL */
bool p = false

/* !<>p automata 
active monitor() {
	never  {
		T0_init:
			do
			:: atomic { ((p)) -> assert(!((p))) }
			:: (1) -> goto T0_init
			od;
		accept_all:
			skip
}
*/

proctype hello() {
	printf("Hello, my name is: %d\n", _pid);
}


init {
	atomic {
		int lastpid;
		lastpid = run hello();
	};
	do
	:: p = true; printf("The p is now %d\n", p);
	:: p = false; printf("The p is now %d\n", p);
	:: break;
	od;
	printf("My time has come");
}
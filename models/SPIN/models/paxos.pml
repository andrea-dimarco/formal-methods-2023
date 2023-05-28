/* DEFINE  PROPERTIES */
ltl consensus { <> consensus_reached }

/* DEFINE MACROS */
#define CHANNEL_LEN 5
#define WAITING_TIME 5
#define N 2
#define A 3
#define L 1
#define Q 2

/* DEFINE TYPES */
mtype = { PREPARE, PROMISE, ACCEPT, LEARN };

/* DEFINE  GLOBAL VARIABLES */
bool consensus_reached = false;

/* DEFINE CHANNELS */
						        // type, r,   v
chan p1_2_a1 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from proposer to acceptor
chan p1_2_a2 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from proposer to acceptor
chan p1_2_a3 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from proposer to acceptor

chan p2_2_a1 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from proposer to acceptor
chan p2_2_a2 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from proposer to acceptor
chan p2_2_a3 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from proposer to acceptor

                                // type, r,   l_r, l_v
chan a1_2_p1 = [CHANNEL_LEN] of { mtype, short, short, short }	// channel from acceptor to proposer
chan a2_2_p1 = [CHANNEL_LEN] of { mtype, short, short, short }	// channel from acceptor to proposer
chan a3_2_p1 = [CHANNEL_LEN] of { mtype, short, short, short }	// channel from acceptor to proposer

chan a1_2_p2 = [CHANNEL_LEN] of { mtype, short, short, short }	// channel from acceptor to proposer
chan a2_2_p2 = [CHANNEL_LEN] of { mtype, short, short, short }	// channel from acceptor to proposer
chan a3_2_p2 = [CHANNEL_LEN] of { mtype, short, short, short }	// channel from acceptor to proposer

                                // type, r,   v
chan a1_2_l1 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from acceptor to learner
chan a2_2_l1 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from acceptor to learner
chan a3_2_l1 = [CHANNEL_LEN] of { mtype, short, short }	        // channel from acceptor to learner

/* DEFINE  PROCESSES */
proctype proposer(chan p_2_a1, p_2_a2, p_2_a3, a1_2_p, a2_2_p, a3_2_p)
{
	/* allocate variables */
	short round;
	short my_val;
	short voting_val;
	short voting_round;
	short n_recv;
	bool recv[A];
	short promise_last_r[A];
	short promise_last_v[A];
	short promised_r;
	short waited;
	short max_round_a;
	short max_round;
	short i;

	/* initialize variables */
	initialize_proposer:
	true;
	d_step {
		promise_last_r[0] = -1;
		promise_last_v[0] = -1;
		promise_last_r[1] = -1;
		promise_last_v[1] = -1;
		promise_last_r[2] = -1;
		promise_last_v[2] = -1;
		recv[0] = false;
		recv[1] = false;
		recv[2] = false;
		n_recv = 0;
		max_round_a = -1;
		max_round = -1;
		i = 0;
		promised_r = -1;
		waited = 0;
	}

	/* choose nondeterministically a value to propose */
	start_proposer:
	round = _pid;
	if 
	:: true -> my_val = 1;
	:: true -> my_val = 2;
	fi;

	/* pick a round to vote in */
	pick_round:
	d_step {
		round = round + N;
		voting_round = round;
		voting_val = my_val;
	};

	/* send prepare messages */
	send_prepare:
	d_step {
		p_2_a1 ! PREPARE, voting_round, my_val;
		p_2_a2 ! PREPARE, voting_round, my_val;
		p_2_a3 ! PREPARE, voting_round, my_val;
	}
	
	/* receive promises */
	recv_promises:
	skip;
	d_step {
		n_recv = 0;
		recv[0] = false; recv[1] = false; recv[2] = false;
		waited = 0;
	}
	do
	:: (waited <= WAITING_TIME) -> 
			//atomic {
				if
				/* receive  from 1st acceptor */
				:: nempty(a1_2_p) ->
						a1_2_p ? PROMISE, promised_r, promise_last_r[0], promise_last_v[0];
						n_recv = n_recv + 1;
						recv[0] = 1;
				/* receive  from 2nd acceptor */
				:: nempty(a2_2_p) ->
						a2_2_p ? PROMISE, promised_r, promise_last_r[1], promise_last_v[1];
						n_recv = n_recv + 1;
						recv[1] = 1;
				/* receive  from 3rd acceptor */
				:: nempty(a3_2_p) ->
						a3_2_p ? PROMISE, promised_r, promise_last_r[2], promise_last_v[2];
						n_recv = n_recv + 1;
						recv[2] = 1;
				:: timeout -> goto start_proposer;
				fi;
			//}
			/* check for quorum */
			if
			:: (recv[0] + recv[1] + recv[2] >= Q) -> break;
			:: else -> skip
			fi;
	:: else -> goto start_proposer;
	od;

	/* choose a value to vote for */
	choose_val:
	i = 0;
	d_step {
		max_round_a = -1;
		max_round = -1;
	}
	do
	:: ((i < A) && recv[i]) -> 
			if
			:: (promise_last_r[i] > max_round) -> d_step { max_round = promise_last_r[i]; max_round_a = i; i = i+1; };
			:: else -> skip
			fi;
	:: ((i < A) && !recv[i]) -> i = i + 1;
	:: else -> break;
	od;
	if
	:: (max_round == -1) -> voting_val = my_val;
	:: else -> voting_val = promise_last_v[max_round_a];
	fi;

	/* send vote */
	send_accept:
	d_step {
		p_2_a1 ! ACCEPT, voting_round, my_val;
		p_2_a2 ! ACCEPT, voting_round, my_val;
		p_2_a3 ! ACCEPT, voting_round, my_val;
	}

	/* end */
	if
	:: false -> goto start_proposer;
	:: else -> true;
	fi;
}

proctype acceptor(chan p1_2_a, p2_2_a, a_2_p1, a_2_p2, a_2_l1)
{
	/* allocate variables */
	short promised_r;
	short last_voted_r;
	short last_voted_v;
	short recv_r;
	short recv_v;
	short send_promise_to;

	/* initialize variables */
	initialize_acceptor:
	skip;
	d_step {
		send_promise_to = -1;
		promised_r = -1;
		last_voted_r = -1;
		last_voted_v = -1;
		recv_r = -1
		recv_v = -1
	}

	/* receive prepares */
	recv_prepare:
	do 
	::  if
		::  nempty(p1_2_a) -> 
				p1_2_a ?? PREPARE, recv_r, recv_v;
				if
				:: (recv_r > promised_r) -> d_step { promised_r = recv_r; send_promise_to = 0;}; goto send_promise;
				:: else -> skip
				fi;
		:: nempty(p2_2_a) -> 
				p2_2_a ?? PREPARE, recv_r, recv_v;
				if
				:: (recv_r > promised_r) -> d_step { promised_r = recv_r; send_promise_to = 1;}; goto send_promise;
				:: else -> skip
				fi;
		fi;
	od;

	/* send promise */
	send_promise:
	if
	:: (send_promise_to == 0) -> a_2_p1 ! PROMISE, promised_r, last_voted_r, last_voted_v;
	:: (send_promise_to == 1) -> a_2_p2 ! PROMISE, promised_r, last_voted_r, last_voted_v;
	:: else -> goto initialize_acceptor; // big problems if this is true
	fi;

	/* receive accept */
	recv_accept:
	do 
	::  if
		::  nempty(p1_2_a) -> 
				p1_2_a ?? ACCEPT, recv_r, recv_v;
				if
				:: (recv_r > promised_r) -> goto send_learn;
				:: else -> skip
				fi;
		:: nempty(p2_2_a) -> 
				p2_2_a ?? ACCEPT, recv_r, recv_v;
				if
				:: (recv_r > promised_r) -> goto send_learn;
				:: else -> skip
				fi;
		fi;
	od;

	/* send learn */
	send_learn:
	skip;
	d_step {
		last_voted_r = recv_r;
		last_voted_v = recv_v;
	}
	a_2_l1 ! LEARN, recv_r, recv_v;
	goto recv_prepare;
}

proctype learner(chan a1_2_l, a2_2_l, a3_2_l)
{
	/* allocate */
	short final_value;
	short voted_r[A];
	short voted_v[A];
	short i;
	short j;
	short count;

	/* initialize */
	initialize_learner:
	d_step {
		final_value = -1;
		consensus_reached = false;
		voted_r[0] = -1;
		voted_v[0] = -1;
		voted_r[1] = -1;
		voted_v[1] = -1;
		voted_r[2] = -1;
		voted_v[2] = -1;
		i = 0; j = 0; count = 0;
	}

	/* receive LEARN */
	recv_learn:
	do 
	:: (!consensus_reached) -> 
			/* get messages */
			if
			:: nempty(a1_2_l) -> 
					a1_2_l ? LEARN, voted_r[0], voted_v[0];
			:: empty(a1_2_l) -> skip
			fi;
			if
			:: nempty(a2_2_l) ->
					a2_2_l ? LEARN, voted_r[1], voted_v[1];
			:: empty(a2_2_l) -> skip
			fi;
			if
			:: nempty(a3_2_l) ->
					a3_2_l ? LEARN, voted_r[2], voted_v[2];
			:: empty(a3_2_l) -> skip
			fi;
			/* check for consensus */
			d_step { i = 0; j = 0; };
			do
			:: (i < A) -> 
					if
					:: (voted_v[i] > -1) ->
							d_step { count = 1; j = i + 1; }
							do
							:: ((j < A) &&  (voted_v[i] == voted_v[j])) -> count = count+1; j = j+1;
							:: ((j < A) && !(voted_v[i] == voted_v[j])) -> j = j+1;
							:: else -> break;
							od;
							if
							:: (count >= Q) -> d_step { consensus_reached = true; final_value = voted_v[i]; }; goto acceptor_end;
							:: else -> skip
							fi;
					:: else -> skip
					fi;
					i = i +1;
			:: else -> break;
			od;
	:: else -> break;
	od;

	/* consensus reached */
	acceptor_end:
	skip
}

/* INITIALIZE */
init{
	/* allocate */
	short p1;
	short p2;
	short a1;
	short a2;
	short a3;
	short l1;

	/* run */
	atomic {
		p1 = run proposer(p1_2_a1, p1_2_a2, p1_2_a3, a1_2_p1, a2_2_p1, a3_2_p1);
		p1 = run proposer(p2_2_a1, p2_2_a2, p2_2_a3, a1_2_p2, a2_2_p2, a3_2_p2);

		a1 = run acceptor(p1_2_a1, p2_2_a1, a1_2_p1, a1_2_p2, a1_2_l1);
		a2 = run acceptor(p1_2_a2, p2_2_a2, a2_2_p1, a2_2_p2, a2_2_l1);
		a3 = run acceptor(p1_2_a3, p2_2_a3, a3_2_p1, a3_2_p2, a3_2_l1);

		l1 = run learner(a1_2_l1, a2_2_l1, a3_2_l1);
	}
}
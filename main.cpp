/* 
	Copyright © 2013 Reagan Lopez
	[This program is licensed under the "MIT License"]
*/

/*****************************************************************/
// main.cpp: Program to find strongly connected components in
// a directed graph. Generates output file scc.txt containing
// original graph, scc including singleton nodes and scc excluding
// singleton nodes.
// Author: Reagan Lopez
// Date: 07/29/2013
/*****************************************************************/
#include <iostream>
#include "stdlib.h"
#include "stdio.h"
#include "iomanip"
#include <fstream>

using namespace std;
typedef struct node_tp * node_ptr_tp;	// announce fwd
typedef struct link_tp * link_ptr_tp;	// announce fwd
int scc_number = 0;	                    // Tarjan's SCC numbers
node_ptr_tp	scc_stack = NULL;	        // stack exists via link in nodes
int scc_count = 0;	                    // tracks number of SCCs
node_ptr_tp finger = NULL;              // LList tail to traverse graph
const char* OUTPUTFILE = "scc.txt";     // output filename
bool single = true;                     // flag to specify with or without singleton nodes
ofstream outfile;                       // output file pointer

#define NIL 0
#define LINK_SIZE sizeof( str_link_tp )
#define NODE_SIZE sizeof( str_node_tp )
#define ASSERT( node , statement )												                    \
	if ( node == NULL ) {                                                                           \
	    cout << "\n" << statement;                                                                  \
	    outfile << "\n" << statement;                                                               \
        exit( 0 );                                                                                  \
	}

// LList of successors; last one connected is the first one inserted.
struct link_tp
{
	link_ptr_tp	next_link;	// point to next link
	node_ptr_tp	next_node;	// point to successor node
} str_link_tp;

// Structure for Graph nodes
struct node_tp
{
	link_ptr_tp	link;		    // points to Llist of successor nodes
	node_ptr_tp	finger;	        // finger through all nodes
	int	lowlink;	            // Tarjan's lowlink
	int	number;	                // Tarjan's number
	int	name;		            // name given during creation
	bool visited;	            // avoid repeat visit
	node_ptr_tp scc_pred;       // pointer to scc predecessor nodes
} str_node_tp;

/*****************************************************************/
// Function to push elements into stack.
// global "scc_stack" simulates stack via Llist in nodes
// each node has scc_pred link, linking up in fashion of a stack
/*****************************************************************/
void push( node_ptr_tp v )
{ // push
	ASSERT( v, "push() called with NIL vertex v" );
	ASSERT( !( v->visited ), "pushing vertex again?" );
	v->scc_pred	= scc_stack;	// first time NULL, then stack ptr
	v->visited	= true;			// will be handled now
	scc_stack	= v;			// global pts ID's head
} //end push

/*****************************************************************/
// Function to pop elements out of stack.
// starting with global scc_stack, traverse whole stack
// all elements are connected by node field scc_stack
/*****************************************************************/
void pop()
{ // pop
	ASSERT( scc_stack, "error, empty SCC stack" );
	scc_stack->visited 	= false; 	// remove from stack
	scc_stack 			= scc_stack->scc_pred;
} //end pop

/*****************************************************************/
// Function to detect SCCs in a directed graph excluding singleton
// nodes.
/*****************************************************************/
void scc( node_ptr_tp v )
{ // scc
	node_ptr_tp w;
	ASSERT( v, "calling scc with NULL pointer" );
	//ASSERT( !v->number, "node already has non-null number!" );
	if ( v->number == NULL ) { //if node already exists in an scc do not print again.
        v->number = v->lowlink = ++scc_number;
        push( v );
        for( link_ptr_tp link=v->link; link; link=link->next_link ) {
                w = link->next_node;
                ASSERT( w, "node w linked as successor must be /= 0" );
                // if number is 0: not yet SCC'ed
                if( ! w->number ) {
                    scc( w );
                    v->lowlink = min( v->lowlink, w->lowlink );
                }else if( w->number < v->number ) {
                    // frond, AKA "cross link"
                    if( w->visited ) {	// visited means: is on stack
                        v->lowlink = min( v->lowlink, w->number );
                    } //end if
                } //end if
        } //end for
        // now see, whether v is part of an SCC and if so, record SCC number and all nodes belonging to it
        if ( v->lowlink == v->number ) {
            if ( !single ) { // exclude singleton nodes
                // found next scc; but if singleton node SCC, then skip it
                if ( scc_stack == v ) {
                    // yes, singleton node; so be silent! Uninteresting!
                    pop();
                }else{
                    // multi-node SCC; So we do consider
                    scc_count++;
                    cout << "SCC number " << scc_count << endl;
                    outfile << "SCC number " << scc_count << endl;
                    while( scc_stack && ( scc_stack->number >= v->number ) ) {
                        cout << scc_stack->name << endl;
                        outfile << scc_stack->name << endl;
                        pop();
                    } //end while
                } //end if
            }else{ // include singleton nodes
                scc_count++;
                cout << "SCC number " << scc_count << endl;
                outfile << "SCC number " << scc_count << endl;
                while( scc_stack && ( scc_stack->number >= v->number ) ) {
                    cout << scc_stack->name << endl;
                    outfile << scc_stack->name << endl;
                    pop();
                } //end while
            } //end if
        } //end if
	}
} //end scc

/*****************************************************************/
// Function to check, whether link between these 2 nodes already
// exists. if not, return true: New! Else return false, NOT new!
/*****************************************************************/
bool new_link( node_ptr_tp first, node_ptr_tp second )
{ // new_link
	int target = second->name;
	link_ptr_tp link = first->link;
	while ( link ) {
        if ( target == link->next_node->name ) {
            return false; // it is an existing link, NOT new
        } //end if
        link = link->next_link; // check next node; if any
	} //end while
	return true; // none of successors equal the second node's name
} //end new_link

/*****************************************************************/
// Function to make link from first node to second node.
// returns link.
/*****************************************************************/
link_ptr_tp make_link( link_ptr_tp	linkhead, node_ptr_tp second )
{ // make_link
    link_ptr_tp temp = ( link_ptr_tp ) malloc( LINK_SIZE );
    temp->next_node = second;
    temp->next_link = linkhead;
    linkhead = temp;
    return linkhead;
} //end make_link

/*****************************************************************/
// Function to make a node.
// create a node in graph G, identified by "name"
// connect to the global "finger" at head of Llist
/*****************************************************************/
node_ptr_tp make_node( int name )
{ // make_node
	node_ptr_tp node = ( node_ptr_tp ) malloc( NODE_SIZE );
	// check once non-Null here, not on user side!
	ASSERT( node, "no space for node in heap!" );
 	node->finger = finger;	    // re-assign finger
	node->lowlink = NIL;		// int. not pointer
	node->number = NIL;		    // int type
	node->link = NULL;		    // pointer type
	node->name = name;		    // IDs this node
	node->visited = false;		// initially
	finger = node;		        // now link to "this"
	return node;
} //end make_node

/*****************************************************************/
// Function to check if a node already exists.
// returns null if does not exists. else return node.
/*****************************************************************/
node_ptr_tp exists( int n )
{ // exists
    node_ptr_tp temp = finger;
    while ( temp ) {
        if ( n == temp->name ) {
            return temp;
        }

        temp = temp->finger;
    }
    return NULL;
} //end exists

/*****************************************************************/
// Function to enter node and edge information.
// input is list of pairs, each element being a node name
// craft edge from first to second name = number
// If a node is new: create it; else use ptr = exists()
/*****************************************************************/
void input( int a, int b )
{
    link_ptr_tp link;
    node_ptr_tp first, second;

    if ( ! ( first = exists( a ) ) ) {	    // 'a' new node?
        first = make_node( a );	            // allocate 'a'
    } //end if

    if ( ! ( second = exists( b ) ) ) {	    // 'b' new node?
        second = make_node( b );			// allocate 'b'
    } //end if

    // both exist. Either created, or pre-existed: Connect!
    if ( new_link( first, second ) ) {
        link = make_link( first->link, second );
        ASSERT( link, "no space for link node" );
        first->link = link;
        if ( single ) outfile << "\n" << first->name << "->" << second->name;
    }else{
        // link was there already, no need to add again!
        if ( single ) printf( "Skipped duplicate link %d->%d\n", a, b );
        if ( single ) outfile << "\nSkipped duplicate link " << a << "->" << b;
    } //end if
} //end input

/*****************************************************************/
// Main function.
/*****************************************************************/
int main()
{
    int a, b, i = 0, ncount = 0;
    int aa[100], bb[100]; //array to store node names
    node_ptr_tp temp = NULL;
    outfile.open( OUTPUTFILE );

    cout << "\nEnter integer node pairs; Enter any letter to exit.\n";
    while( scanf( "%d%d", &a, &b ) ) {
        aa[i] = a;
        bb[i] = b;
        i++;
    }
    ncount = --i; //get count of nodes

    outfile << "\nOriginal Graph:";
    outfile << "\n---------------";
    for ( i = 0; i <= ncount; i++ ) {
        input( aa[i], bb[i] ); //create original graph but no print
    }

	cout << "\n\nSCC including singleton nodes:\n";
	outfile << "\n\nSCC including singleton nodes:";
	outfile << "\n------------------------------\n";
	temp = finger;
	while ( temp!=NULL ) {
        if ( temp->visited == false ) {
            scc( temp ); //call scc with singleton node flag set to true
        }
        temp = temp->finger;
	}

	cout << "\nSCC excluding singleton nodes:\n";
	outfile << "\nSCC excluding singleton nodes:";
	outfile << "\n------------------------------\n";
    single = false;     //set singleton node flag to false
	scc_stack = NULL;   //reset stack
    scc_count = 0;      //reset scc_count
    scc_number = 0;     //reset scc_number
    finger = NULL;      //reset finger
    for ( i = 0; i <= ncount; i++ ) {
        input( aa[i], bb[i] ); //enter the node pairs
    }
    temp = finger;
	while ( temp!=NULL ) {
        if ( temp->visited == false ) {
            scc( temp ); //call scc with singleton node flag set to false
        }
        temp = temp->finger;
	}
    outfile.close();
    return 0;
}

#include <bits/stdc++.h>

using namespace std;

// Types for representing graph vertices and edges
typedef uint8_t vertex_t;
typedef pair<vertex_t, vertex_t> edge_t;

// Type for representing discrete finite automata
typedef size_t state_t;
typedef vertex_t event_t;

// Because vector<bool> is templated specially and breaks things
typedef vector<uint8_t> vecbool;

// A vaguely decent hash combinator to simplify hashing collection types
template <typename T>
inline void hash_combine(size_t& h, T const& v) { h ^= hash<T>()(v) + 0x9e3779b9 + (h << 6) + (h >> 2); }

// Templated hash implementation for pair
template<typename T, typename U>
struct hash<pair<T, U>> {
	size_t operator() (pair<T, U> const& v) const {
		size_t result = 0;
		hash_combine(result, v.first);
		hash_combine(result, v.second);
		return result;
	}
};

// Templated hash implementation for vector
template<typename T>
struct hash<vector<T>> {
	size_t operator() (vector<T> const& v) const {
		size_t result = 0;
		for (auto& item : v) hash_combine(result, item);
		return result;
	}
};

// Explicit transition table representation of DFA
// Assumes pseudocyclic
// Assumes alphabet is in sorted order
// Assumes states are toposorted with initial state at end,
// so postorder DFS will visit states in increasing index
// Uses max val to represent self-loops
#define SELF_LOOP (numeric_limits<state_t>::max())
struct DFA {
	vector<event_t> alphabet;	// Alphabet for DFA
	vector<vector<state_t>> transitions;	// Explicit transition table indexed by event_t
	vecbool accepting;	// Boolean array to mark each state as accepting or not

	// Construct a 1-state empty-alphabet DFA with given accepting
	DFA(bool acc = false) : transitions(1), accepting(1, acc) {}

	// Construct DFA from internal representation
	DFA(vector<vertex_t> ab,
		vector<vector<state_t>> table,
		vecbool acc) :
		alphabet(ab),
		transitions(table),
		accepting(acc)
	{}

	// Construct DFA with given alphabet and given number of states, containing only self-loops and no accepting states
	DFA(vector<vertex_t> ab, size_t states) :
		alphabet(ab),
		transitions(states, vector<state_t>(ab.size(), SELF_LOOP)),
		accepting(states)
	{}

	// Used to sanity check human-made inputs
	bool is_valid() const {
		if (transitions.size() != accepting.size()) return false;
		if (!is_sorted(alphabet.begin(), alphabet.end())) return false;
		if (adjacent_find(alphabet.begin(), alphabet.end()) != alphabet.end()) return false;
		for (int parent = 0; parent < transitions.size(); ++parent) {
			if (transitions[parent].size() != alphabet.size()) return false;
			for (auto child : transitions[parent]) {
				if (child > parent && child != SELF_LOOP) return false;
			}
		}
		return true;
	}

	// Mark the specified state as accepting (or not, as given)
	void set_accepting(state_t state, bool acc = true) {
		assert(0 <= state && state < accepting.size());
		accepting[state] = acc;
	}

	// Update transition table to represent specified transition
	void add_transition(state_t from, event_t event, state_t to) {
		assert(0 <= from && from < transitions.size());
		assert(0 <= to && to < transitions.size() || to == SELF_LOOP);
		assert(to != from);
		auto bounds = equal_range(alphabet.begin(), alphabet.end(), event);	// Find index of event in alphabet
		assert(bounds.first != bounds.second);
		size_t event_id = bounds.first - alphabet.begin();
		assert(event_id < transitions[from].size());
		transitions[from][event_id] = to;
	}

	// Helper function to retrieve initial state
	state_t init_state() const {
		return transitions.size() - 1;
	}

	// Helper function to retrieve new state after a given event id
	// Defaults to a self-loop if the event is unknown
	state_t transition(state_t curr, size_t event_id) const {
		return (event_id < alphabet.size()) ? transitions[curr][event_id] : SELF_LOOP;
	}

	// private
	// DFS the DFA to find the lexicographically minimum accepting sequence
	bool dfs(vector<event_t>& sequence, vecbool& visited, state_t curr) {
		if (visited[curr]) return false;
		visited[curr] = true;

		if (accepting[curr]) return true;

		vector<state_t>& row = transitions[curr];
		for (size_t i = 0; i < alphabet.size(); ++i) {
			state_t next = row[i] == SELF_LOOP ? curr : row[i];	// Could be min(curr, row[i])?
			sequence.push_back(alphabet[i]);
			if (dfs(sequence, visited, next)) return true;
			sequence.pop_back();
		}

		return false;
	}

	// Find the lexicographically least accepting sequence
	pair<bool, vector<event_t>> find_solution() {
		size_t states = transitions.size();
		vector<event_t> sequence;
		vecbool visited(states, false);
		return make_pair(dfs(sequence, visited, states-1), sequence);
	}

	// Parallel DFS DP from initial states through this and rhs
	// Add states as required to maintain toposort
	// Simplify states by behavioural equivalence as we go
	DFA operator&&(const DFA &rhs) const {
		const DFA &lhs = *this;

		// Compute alphabet for new automaton
		vector<event_t> alphabet;
		set_union(lhs.alphabet.begin(), lhs.alphabet.end(), rhs.alphabet.begin(), rhs.alphabet.end(), back_inserter(alphabet));

		// Compute mappings between old and new event ids
		vector<size_t> from_lhs_ev(lhs.alphabet.size()), to_lhs_ev(alphabet.size(), SELF_LOOP);
		vector<size_t> from_rhs_ev(rhs.alphabet.size()), to_rhs_ev(alphabet.size(), SELF_LOOP);
		for (size_t ai = 0, li = 0, ri = 0; ai < alphabet.size(); ++ai) {
			if (li < lhs.alphabet.size() && lhs.alphabet[li] == alphabet[ai]) {
				from_lhs_ev[li] = ai;
				to_lhs_ev[ai] = li++;
			}
			if (ri < rhs.alphabet.size() && rhs.alphabet[ri] == alphabet[ai]) {
				from_rhs_ev[ri] = ai;
				to_rhs_ev[ai] = ri++;
			}
		}

		vector<vector<state_t>> transitions;
		vecbool accepting;

		unordered_map<pair<vector<state_t>, bool>, state_t> behaviour_ids;	// Map from state behaviour to new state
		unordered_map<pair<state_t, state_t>, state_t> compress;	// Map from state pairs to new state, if known

		// Perform explicit iterative DFS to implement top-down dynamic programming
		// Stack elements represent ((left state, right state), seen)
		// A state is seen if we have started solving it, even if not finished
		stack<pair<pair<state_t, state_t>, bool>> dpstack;
		dpstack.push(make_pair(make_pair(lhs.init_state(), rhs.init_state()), false));

		while (!dpstack.empty()) {
			pair<state_t, state_t> curr;
			bool seen;
			tie(curr, seen) = dpstack.top(); dpstack.pop();
			state_t ls, rs;
			tie(ls, rs) = curr;

			if (!seen) {	// First time seeing this state
				// Mark as seen and put back on stack so we can solve later
				dpstack.push(make_pair(curr, true));

				// Add all unsolved children to the stack to be solved before we can solve current state
				for (size_t ai = 0; ai < alphabet.size(); ++ai) {
					state_t lc = lhs.transition(ls, to_lhs_ev[ai]);
					state_t rc = rhs.transition(rs, to_rhs_ev[ai]);
					if (lc == SELF_LOOP) lc = ls;
					if (rc == SELF_LOOP) rc = rs;
					auto child = make_pair(lc, rc);
					if (child == curr) continue;
					if (compress.count(child)) continue;
					dpstack.push(make_pair(child, false));
				}
			} else if (!compress.count(curr)) {
				// Check if equivalent state already exists
				// Note must consider being equivalent to children by replacing transitions to each unique child with self-loop
				// However, since we know the result must have a toposort, we can't possibly be equivalent to anything other than our highest child

				// Compute behaviour of this row, and keep hold of highest child we have
				vector<state_t> row(alphabet.size(), SELF_LOOP);
				state_t highest_child = numeric_limits<state_t>::max();
				for (size_t ai = 0; ai < alphabet.size(); ++ai) {
					state_t lc = lhs.transition(ls, to_lhs_ev[ai]);
					state_t rc = rhs.transition(rs, to_rhs_ev[ai]);
					if (lc == SELF_LOOP) lc = ls;
					if (rc == SELF_LOOP) rc = rs;
					auto child = make_pair(lc, rc);
					if (child != curr) {
						row[ai] = compress[child];
						if (row[ai] > highest_child || highest_child == numeric_limits<state_t>::max()) highest_child = row[ai];
					}
				}
				bool acc = lhs.accepting[ls] && rhs.accepting[rs];
				auto behaviour = make_pair(row, acc);

				if (behaviour_ids.count(behaviour)) {	// If we have seen this behaviour before we are obviously equivalent
					compress.emplace(curr, behaviour_ids[behaviour]);	// Map this state to its existing equivalent
				} else {	// Consider possibility of being equivalent to highest child
					auto candidate = row;	// Compute behaviour if we are equivalent to our highest child
					replace(candidate.begin(), candidate.end(), highest_child, SELF_LOOP);	// Replace any transitions to highest child with self-loop
					if (highest_child != numeric_limits<state_t>::max() && acc == accepting[highest_child] && candidate == transitions[highest_child]) {
						compress.emplace(curr, highest_child);	// If we are equivalent to highest child just use that
					} else {	// Otherwise, this is a new unique state, add it on top
						state_t id = transitions.size();
						transitions.push_back(row);
						accepting.push_back(acc);
						behaviour_ids.emplace(behaviour, id);
						compress.emplace(curr, id);
					}
				}
			}
		}

		// cerr << alphabet.size() << ", " << transitions.size() << endl;

		auto result = DFA(alphabet, transitions, accepting);
		// assert(result.is_valid());
		return result;
	}
};

// Construct DFA for given edge (u, v) requiring subsequence uvu exists
DFA half_edge_dfa(edge_t edge) {
	vertex_t u, v;
	tie(u, v) = edge;
	vector<vertex_t> alphabet({u, v});
	sort(alphabet.begin(), alphabet.end());
	DFA result(alphabet, 4);
	result.add_transition(3, u, 2);
	result.add_transition(2, v, 1);
	result.add_transition(1, u, 0);
	result.set_accepting(0);
	assert(result.is_valid());
	return result;
}

// Construct DFA for given edge (u, v) requiring subsequence uvuv DOES NOT exist
DFA no_half_edge_dfa(edge_t edge) {
	vertex_t u, v;
	tie(u, v) = edge;
	vector<vertex_t> alphabet({u, v});
	sort(alphabet.begin(), alphabet.end());
	DFA result(alphabet, 5);
	result.add_transition(4, u, 3);	result.set_accepting(4);
	result.add_transition(3, v, 2);	result.set_accepting(3);
	result.add_transition(2, u, 1);	result.set_accepting(2);
	result.add_transition(1, v, 0);	result.set_accepting(1);
	assert(result.is_valid());
	return result;
}

// Construct a PCG recognition DFA for the given graph
DFA graph_to_dfa(set<vertex_t> vs, set<edge_t> es) {
	for (auto e : es) es.emplace(e.second, e.first);	// Split edges into half-edges
	DFA result(true);
	for (auto u : vs) {
		DFA row_dfa(true);	// Taking the conjunction of each row separately simplifies DFAs because they all start the same
		for (auto v : vs) if (u != v) {
			edge_t e(u, v);
			if (es.count(e)) {
				row_dfa = row_dfa && half_edge_dfa(e);
			} else {
				row_dfa = row_dfa && no_half_edge_dfa(e);
			}
		}
		result = result && row_dfa;
	}
	return result;
}

// Construct a random set of edges with given density for testing
set<edge_t> random_edge_set(set<vertex_t> vs, double density = 0.5) {
	vector<edge_t> vs_squared;
	for (auto u : vs) for (auto v : vs) if (u < v) vs_squared.push_back(make_pair(u, v));
	// srand(time(0));
	random_shuffle(vs_squared.begin(), vs_squared.end());
	auto it = vs_squared.begin();
	int num_edges = round(vs_squared.size() * density);
	set<edge_t> result;
	for (int i = 0; i < num_edges; ++i) result.insert(*it++);
	return result;
}

void run() {
	set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E', 'F' };
	set<edge_t> es = {
		{ 'A', 'B' },
		{ 'A', 'C' },
		{ 'A', 'D' },
		{ 'B', 'C' },
		{ 'B', 'E' },
		{ 'C', 'F' },
		{ 'D', 'E' },
		{ 'D', 'F' },
		{ 'E', 'F' },
	};

	// set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E' };
	// set<edge_t> es = {
	// 	{ 'A', 'B' },
	// 	{ 'A', 'C' },
	// 	{ 'A', 'D' },
	// 	{ 'B', 'C' },
	// 	{ 'B', 'E' },
	// 	{ 'D', 'E' },
	// };

	// set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J' };
	// set<edge_t> es = random_edge_set(vs);

	DFA dfa = graph_to_dfa(vs, es);

	cout << "num states = " << dfa.transitions.size() << endl;
	cout << "alphabet size = " << dfa.alphabet.size() << endl;

	auto p = dfa.find_solution();
	if (p.first) {
		cout << "Found solution: ";
		for (event_t e : p.second) cout << e;
		cout << endl;
	} else {
		cout << "No solution found" << endl;
	}
}

int main() {
	run();
}
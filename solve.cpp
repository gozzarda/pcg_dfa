#include <bits/stdc++.h>

using namespace std;

typedef uint8_t vertex_t;
typedef pair<vertex_t, vertex_t> edge_t;

typedef size_t state_t;
typedef vertex_t event_t;

typedef vector<uint8_t> vecbool;

template <typename T>
inline void hash_combine(size_t& h, T const& v) { h ^= hash<T>()(v) + 0x9e3779b9 + (h << 6) + (h >> 2); }

template<typename T, typename U>
struct hash<pair<T, U>> {
	size_t operator() (pair<T, U> const& v) const {
		size_t result = 0;
		hash_combine(result, v.first);
		hash_combine(result, v.second);
		return result;
	}
};

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
// Assumes states are toposorted with initial state at end
// Uses max val to represent self-loops
// Assumes alphabet is in sorted order
const state_t self_loop = numeric_limits<state_t>::max();
struct DFA {
	vector<event_t> alphabet;
	vector<vector<state_t>> transitions;
	vecbool accepting;

	DFA(bool acc = false) : transitions(1), accepting(1, acc) {}

	DFA(vector<vertex_t> ab,
		vector<vector<state_t>> table,
		vecbool acc) :
		alphabet(ab),
		transitions(table),
		accepting(acc)
	{}

	DFA(vector<vertex_t> ab, size_t states) :
		alphabet(ab),
		transitions(states, vector<state_t>(ab.size(), self_loop)),
		accepting(states)
	{}

	void set_accepting(state_t state, bool acc = true) {
		accepting[state] = acc;
	}

	void add_transition(state_t from, event_t event, state_t to) {
		assert(0 <= from && from < transitions.size());
		assert(0 <= to && to < transitions.size() || to == self_loop);
		assert(to != from);
		auto bounds = equal_range(alphabet.begin(), alphabet.end(), event);
		assert(bounds.first != bounds.second);
		size_t event_id = bounds.first - alphabet.begin();
		assert(event_id < transitions[from].size());
		transitions[from][event_id] = to;
	}

	state_t init_state() const {
		return transitions.size() - 1;
	}

	state_t transition(state_t curr, size_t event_id) const {
		return (event_id < alphabet.size()) ? transitions[curr][event_id] : self_loop;
	}

	// Used to sanity check human-made inputs
	void assert_valid() const {
		assert(transitions.size() == accepting.size());
		assert(is_sorted(alphabet.begin(), alphabet.end()));
		assert(adjacent_find(alphabet.begin(), alphabet.end()) == alphabet.end());
		for (int parent = 0; parent < transitions.size(); ++parent) {
			assert(transitions[parent].size() == alphabet.size());
			for (auto child : transitions[parent]) {
				assert(child <= parent || child == self_loop);
			}
		}
	}

	//private
	bool dfs(vector<event_t>& sequence, vecbool& visited, state_t curr) {
		if (visited[curr]) return false;
		visited[curr] = true;

		if (accepting[curr]) return true;

		vector<state_t>& row = transitions[curr];
		for (size_t i = 0; i < alphabet.size(); ++i) {
			state_t next = row[i] == self_loop ? curr : row[i];	// Could be min(curr, row[i])?
			sequence.push_back(alphabet[i]);
			if (dfs(sequence, visited, next)) return true;
			sequence.pop_back();
		}

		return false;
	}

	pair<bool, vector<event_t>> find_solution() {
		size_t states = transitions.size();
		vector<event_t> sequence;
		vecbool visited(states, false);
		return make_pair(dfs(sequence, visited, states-1), sequence);
	}

	// TODO: continue rework from here
	// Parallel DFS from last state
	// Add states as required to maintain toposort
	// Simplify states by equivalence as we go
	DFA operator&&(const DFA &rhs) const {
		const DFA &lhs = *this;

		// Compute alphabet for new automaton
		vector<event_t> alphabet;
		set_union(lhs.alphabet.begin(), lhs.alphabet.end(), rhs.alphabet.begin(), rhs.alphabet.end(), back_inserter(alphabet));

		// Compute mappings between old and new event ids
		vector<size_t> from_lhs_ev(lhs.alphabet.size()), to_lhs_ev(alphabet.size(), self_loop);
		vector<size_t> from_rhs_ev(rhs.alphabet.size()), to_rhs_ev(alphabet.size(), self_loop);
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

		unordered_map<pair<vector<state_t>, bool>, state_t> behaviour_ids;
		unordered_map<pair<state_t, state_t>, state_t> compress;
		unordered_set<pair<state_t, state_t>> seen;

		stack<pair<state_t, state_t>> state_stack;
		state_stack.push(make_pair(lhs.init_state(), rhs.init_state()));

		while (!state_stack.empty()) {
			auto curr = state_stack.top(); state_stack.pop();
			state_t ls, rs;
			tie(ls, rs) = curr;

			if (!seen.count(curr)) {
				seen.insert(curr);

				state_stack.push(curr);

				// Add all unseen children to the stack
				for (size_t ai = 0; ai < alphabet.size(); ++ai) {
					state_t lc = lhs.transition(ls, to_lhs_ev[ai]);
					state_t rc = rhs.transition(rs, to_rhs_ev[ai]);
					if (lc == self_loop) lc = ls;
					if (rc == self_loop) rc = rs;
					auto child = make_pair(lc, rc);
					if (child == curr) continue;
					if (compress.count(child)) continue;
					state_stack.push(child);
				}
			} else if (!compress.count(curr)) {
				// Check if equivalent state already exists
				// Note may be equivalent to highest child
				// Can't be equivalent to lower children without breaking toposort, which we know isn't the case
				vector<state_t> row(alphabet.size(), self_loop);
				state_t highest_child = self_loop;
				for (size_t ai = 0; ai < alphabet.size(); ++ai) {
					state_t lc = lhs.transition(ls, to_lhs_ev[ai]);
					state_t rc = rhs.transition(rs, to_rhs_ev[ai]);
					if (lc == self_loop) lc = ls;
					if (rc == self_loop) rc = rs;
					auto child = make_pair(lc, rc);
					if (child != curr) {
						row[ai] = compress[child];
						if (row[ai] < highest_child || highest_child == self_loop) highest_child = row[ai];
					}
				}

				bool acc = lhs.accepting[ls] && rhs.accepting[rs];
				auto behaviour = make_pair(row, acc);
				if (behaviour_ids.count(behaviour)) {	// If we have seen this behaviour before we are obviously equivalent
					compress.emplace(curr, behaviour_ids[behaviour]);
				} else {
					auto candidate = row;	// Compute behaviour if we are equivalent to our highest child
					replace(candidate.begin(), candidate.end(), highest_child, self_loop);
					if (highest_child != self_loop && acc == accepting[highest_child] && candidate == transitions[highest_child]) {
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

		return DFA(alphabet, transitions, accepting);
	}
};

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
	result.assert_valid();
	return result;
}

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
	result.assert_valid();
	return result;
}

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

set<edge_t> random_edge_set(set<vertex_t> vs, size_t num_edges, size_t seed = 0) {
	vector<edge_t> all_edges;
	for (auto u : vs) for (auto v : vs) if (u < v) all_edges.push_back(edge_t(u, v));
	default_random_engine rng(seed);
	shuffle(all_edges.begin(), all_edges.end(), rng);
	auto it = all_edges.begin();
	num_edges = min(num_edges, all_edges.size());
	set<edge_t> result;
	for (int i = 0; i < num_edges; ++i) result.insert(*it++);
	return result;
}

pair<set<vertex_t>, set<edge_t>> random_graph(size_t num_verts, size_t num_edges, size_t seed = 0) {
	set<vertex_t> vs;
	for (size_t v = 0; v < num_verts; ++v) vs.insert('A' + v);
	set<edge_t> es = random_edge_set(vs, num_edges, seed);
	return {vs, es};
}

void cerr_graph(set<vertex_t> vs, set<edge_t> es) {
	cerr << ' ';
	for (auto v : vs) cerr << ' ' << v;
	cerr << endl;
	for (auto u : vs) {
		cerr << u;
		for (auto v : vs) {
			edge_t e(u, v), r(v, u);
			cerr << ' ' << (es.count(e) || es.count(r));
		}
		cerr << endl;
	}
}

// Should probably replace with just generating a connected graph in the first place, but this is easier
bool is_connected_graph(set<vertex_t> vs, set<edge_t> es) {
	set<vertex_t> seen;
	seen.insert(*vs.begin());
	for (int i = 0; i < vs.size() && seen.size() < vs.size(); ++i) {
		for (edge_t e : es) {
			if (seen.count(e.first)) seen.insert(e.second);
			if (seen.count(e.second)) seen.insert(e.first);
		}
	}
	return seen.size() == vs.size();
}

void timestats() {
	default_random_engine rng;
	uniform_int_distribution<size_t> vdist(5, 7);
	const string sep = "\t";
	cout << "V" << sep << "E" << sep << "seed (hex)" << sep << "states" << sep << "runtime (ms)" << endl;
	while (true) {
		size_t num_verts = vdist(rng);
		uniform_int_distribution<size_t> edist(num_verts - 1, num_verts * (num_verts - 1) / 2);
		size_t num_edges = edist(rng);
		set<vertex_t> vs;
		set<edge_t> es;
		size_t seed = rng();
		tie(vs, es) = random_graph(num_verts, num_edges, seed);
		if (!is_connected_graph(vs, es)) continue;
		cerr << num_verts << sep << num_edges << sep << hex << seed << dec << endl;
		cerr_graph(vs, es);
		auto init_time = chrono::high_resolution_clock::now();
		DFA dfa = graph_to_dfa(vs, es);
		auto halt_time = chrono::high_resolution_clock::now();
		auto runtime = chrono::duration_cast<chrono::milliseconds>(halt_time - init_time);
		cerr << "num states = " << dfa.transitions.size() << endl;
		auto p = dfa.find_solution();
		if (p.first) {
			cerr << "Found solution: ";
			for (event_t e : p.second) cerr << e;
			cerr << endl;
		} else {
			cerr << "No solution found" << endl;
		}
		cout << num_verts << sep << num_edges << sep << hex << seed << dec << sep << dfa.transitions.size() << sep << runtime.count() << endl;
	}
}

void run() {
	// set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E', 'F' };
	// set<edge_t> es = {
	// 	{ 'A', 'B' },
	// 	{ 'A', 'C' },
	// 	{ 'A', 'D' },
	// 	{ 'B', 'C' },
	// 	{ 'B', 'E' },
	// 	{ 'C', 'F' },
	// 	{ 'D', 'E' },
	// 	{ 'D', 'F' },
	// 	{ 'E', 'F' },
	// };

	// set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E' };
	// set<edge_t> es = {
	// 	{ 'A', 'B' },
	// 	{ 'A', 'C' },
	// 	{ 'A', 'D' },
	// 	{ 'B', 'C' },
	// 	{ 'B', 'E' },
	// 	{ 'D', 'E' },
	// };

	set<vertex_t> vs;
	set<edge_t> es;
	tie(vs, es) = random_graph(10, 28, 0xbc5816b);
	cerr_graph(vs, es);

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
	// run();
	timestats();
}
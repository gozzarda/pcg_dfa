#include <bits/stdc++.h>

using namespace std;

typedef uint8_t vertex_t;
typedef pair<vertex_t, vertex_t> edge_t;

typedef size_t state_t;
typedef vertex_t event_t;

typedef vector<uint8_t> vecbool;

// struct pair_hash {
// 	template <class T1, class T2>
// 	size_t operator() (const pair<T1, T2> &p) const { return (hash<T1>()(p.first) << 1) ^ hash<T2>()(p.second); }
// };

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

	size_t init_state() const {
		return transitions.size() - 1;
	}

	size_t transition(state_t curr, size_t event_id) const {
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
			if (lhs.alphabet[li] == alphabet[ai]) {
				from_lhs_ev[li] = ai;
				to_lhs_ev[ai] = li++;
			}
			if (rhs.alphabet[ri] == alphabet[ai]) {
				from_rhs_ev[ri] = ai;
				to_rhs_ev[ai] = ri++;
			}
		}

		vector<vector<state_t>> transitions;
		vecbool accepting;

		map<pair<vector<state_t>, bool>, state_t> behaviour_ids;
		map<pair<state_t, state_t>, state_t> compress;

		set<pair<state_t, state_t>> seen, done;

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
					if (done.count(child)) continue;
					state_stack.push(child);
				}
			} else if (!done.count(curr)) {
				done.insert(curr);

				// Check if equivalent state already exists
				// Note may be equivalent to highest child
				// Can't be equivalent to lower children without breaking toposort, which we know isn't the case
				bool acc = lhs.accepting[ls] && rhs.accepting[rs];
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

		return DFA(alphabet, transitions, accepting);
	}

	static DFA conjunction(vector<DFA>::const_iterator lwr, vector<DFA>::const_iterator upr) {
		if (next(lwr) == upr) return *lwr;
		auto mid = lwr + distance(lwr, upr) / 2;
		return conjunction(lwr, mid) && conjunction(mid, upr);
	}
};

DFA edge_to_dfa_parity(edge_t edge) {
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

DFA exclude_edge_to_dfa_parity(edge_t edge) {
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
	for (auto e : es) es.insert(make_pair(e.second, e.first));
	set<edge_t> vs_squared;
	for (auto u : vs) for (auto v : vs) if (u != v) vs_squared.insert(make_pair(u, v));
	vector<edge_t> es_prime;
	set_difference(vs_squared.begin(), vs_squared.end(), es.begin(), es.end(), back_inserter(es_prime));

	vector<DFA> dfas;
	transform(es.rbegin(), es.rend(), back_inserter(dfas), edge_to_dfa_parity);
	transform(es_prime.begin(), es_prime.end(), back_inserter(dfas), exclude_edge_to_dfa_parity);
	random_shuffle(dfas.begin(), dfas.end());	// Avoid expensive structures
	return DFA::conjunction(dfas.begin(), dfas.end());
}

set<edge_t> random_edge_set(set<vertex_t> vs, double density = 0.5) {
	vector<edge_t> vs_squared;
	for (auto u : vs) for (auto v : vs) if (u < v) vs_squared.push_back(make_pair(u, v));
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

	// set<vertex_t> vs = { 'A', 'B', 'C', 'D', 'E', 'F' };
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
#include <bits/stdc++.h>

using namespace std;

typedef uint8_t vertex_t;
typedef pair<vertex_t, vertex_t> edge_t;

typedef size_t state_t;
typedef vertex_t event_t;

typedef vector<uint8_t> vecbool;

// Explicit transition table representation of DFA
// Assumes pseudocyclic
// Assumes states are toposorted with initial state at end
// Uses max val to represent self-loops
// Assumes alphabet is in sorted order
struct DFA {
	const state_t self_loop = numeric_limits<state_t>::max();

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
		accepting(states),
		transitions(states, vector<state_t>(ab.size(), self_loop))
	{}

	void set_accepting(state_t state, bool acc = true) {
		accepting[state] = acc;
	}

	void add_transition(state_t from, event_t event, state_t to) {
		auto bounds = equal_range(alphabet.begin(), alphabet.end(), event);
		assert(bounds.first != bounds.second);
		size_t event_id = *bounds.first
		transitions[from][event_id] = to;
	}

	size_t init_state() const {
		return transitions.size() - 1;
	}

	// Used to sanity check human-made inputs
	bool validate() const {
		if (transitions.size() != accepting.size()) return false;
		if (!is_sorted(alphabet.begin(), alphabet.end())) return false;
		if (adjacent_find(alphabet.begin(), alphabet.end()) != alphabet.end()) return false
		for (int parent = 0; parent < transitions.size(); ++parent) {
			if (transitions[parent].size() != alphabet.size()) return false;
			for (auto child : transitions[parent]) {
				if (child > parent && child != self_loop) return false;
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

		unordered_map<pair<vector<state_t>, bool>, state_t> behaviour_ids;
		unordered_map<pair<state_t, state_t>, state_t> compress;

		unordered_set<pair<state_t, state_t>> seen;

		stack<pair<state_t, state_t>> state_stack;
		stack<bool> visited_stack;
		state_stack.push(make_pair(lhs.init_state(), rhs.init_state()));
		visited_stack.push(false);
		seen.insert(s.top());

		while (!s.empty()) {
			auto curr = state_stack.top(); state_stack.pop();
			bool visited = visited_stack.top(); visited_stack.pop();
			state_t ls, rs;
			tie(ls, rs) = curr;

			if (!visited) {
				state_stack.push(curr);
				visited_stack.push(true);

				// Add all unseen children to the stack
				for (size_t ai = 0; ai < alphabet.size(); ++ai) {
					state_t lc = lhs.transitions[ls][to_lhs_ev[ai]];
					state_t rc = rhs.transitions[rs][to_rhs_ev[ai]];
					auto child = make_pair(lc, rc);
					if (seen.count(child)) continue;
					seen.insert(child);
					state_stack.push(child);
				}
			} else {
				// Check if equivalent state already exists
				// Note may be equivalent to highest child
				// Can't be equivalent to lower children without breaking toposort, which we know isn't the case
				bool acc = lhs.accepting[ls] && rhs.accepting[rs];
				vector<state_t> row(alphabet.size(), self_loop);
				state_t highest_child = 0;
				for (size_t ai = 0; ai < alphabet.size(); ++ai) {
					state_t lc = lhs.transitions[ls][to_lhs_ev[ai]];
					state_t rc = rhs.transitions[rs][to_rhs_ev[ai]];
					auto child = make_pair(lc, rc);
					if (child != curr) {
						row[ai] = compress[child];
						highest_child = max(highest_child, row[ai]);
					}
				}

				auto behaviour = make_pair(row, acc);
				if (behaviour_ids.count(behaviour)) {	// If we have seen this behaviour before we are obviously equivalent
					compress.emplace(curr, behaviour_ids[behaviour]);
				} else {
					auto candidate = row;	// Compute behaviour if we are equivalent to our highest child
					replace(candidate.begin(), candidate.end(), highest_child, self_loop);
					if (acc == accepting[highest_child] && candidate == transitions[highest_child]) {
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

	static DFA conjunction(vector<DFA>::iterator lwr, vector<DFA>::iterator upr) {
		if (next(lwr) == upr) return *lwr;
		auto mid = lwr + distance(lwr, upr) / 2;
		return conjunction(lwr, mid) && conjunction(mid, upr);
	}
};

DFA edge_to_dfa_parity(edge_t edge) {
	vertex_t u, v;
	tie(u, v) = edge;
	vector<vertex_t> alphabet(u, v);
	sort(alphabet.begin(), alphabet.end());
	DFA result(alphabet, 4);
	result.add_transition(3, u, 2);
	result.add_transition(2, v, 1);
	result.add_transition(1, u, 0);
	result.set_accepting(0);
	return result;
}

DFA exclude_edge_to_dfa_parity(edge_t edge) {
	vertex_t u, v;
	tie(u, v) = edge;
	vector<vertex_t> alphabet(u, v);
	sort(alphabet.begin(), alphabet.end());
	DFA result(alphabet, 5);
	result.add_transition(4, u, 3);	result.set_accepting(4, true);
	result.add_transition(3, v, 2);	result.set_accepting(3, true);
	result.add_transition(2, u, 1);	result.set_accepting(2, true);
	result.add_transition(1, v, 0);	result.set_accepting(1, true);
	return result;
}

DFA graph_to_dfa(set<vertex_t> vs, set<edge_t> es) {
	for (auto e : es) es.insert(make_pair(e.second, e.first));
	set<edge_t> vs_squared;
	for (auto u : vs) for (auto v : vs) if (u != v) vs_squared.insert(make_pair(u, v));
	vector<edge_t> es_prime;
	set_difference(vs_squared.begin(), vs_squared.end(), es.begin(), es.end(), inserter(es_prime, es_prime.end()));

	vector<DFA> dfas;
	transform(es.begin(), es.end(), back_inserter(dfas), edge_to_dfa_parity);
	transform(es_prime.begin(), es_prime.end(), back_inserter(dfas), exclude_edge_to_dfa_parity);
	random_shuffle(dfas.begin(), dfas.end());	// Avoid expensive structures
	// for (auto lwr = dfas.begin(), upr = prev(dfas.end()); lwr < upr; lwr += 2, upr -= 2) {
	// 	swap(*lwr, *upr);
	// }
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
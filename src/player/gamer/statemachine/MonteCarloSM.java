package player.gamer.statemachine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.prover.ProverStateMachine;

public class MonteCarloSM extends StateMachineGamer {

	private static final int MAX_SCORE = 100;
	private static final int TIMEOUT_BUFFER = 500;
	private long _timeout;
	Random generator = new Random();


	private List<Role> _opp_roles;
	private HashMap<MachineState,Integer> _cache;

	private class Move_Node {
		public int value;
		public Move move;
		public Move_Node(int value, Move move){
			this.value = value;
			this.move = move;
		}
	}

	@Override
	public StateMachine getInitialStateMachine() {	
		return new ProverStateMachine();
	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		_timeout = timeout - TIMEOUT_BUFFER;
		_opp_roles = new ArrayList<Role>();
		_cache = new HashMap<MachineState,Integer>();
		ArrayList<Role> all_roles = (ArrayList<Role>) getStateMachine().getRoles();
		for(int i=0; i<all_roles.size(); i++){
			if(!(getRole().equals(all_roles.get(i)))){
				_opp_roles.add(all_roles.get(i));
			}
		}

	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		_timeout = timeout - TIMEOUT_BUFFER;
		List<Move> legalMoves = getStateMachine().getLegalMoves(getCurrentState(), getRole());
		if(legalMoves.size()==1){
			return(legalMoves.get(0));
		}
		Move move = getValue_Monte(getCurrentState());
		if(move == null) return legalMoves.get(0);
		return(move);
	}

	private Move getValue_Monte(MachineState currState) throws MoveDefinitionException {
		List<Move> legalMoves = getStateMachine().getLegalMoves(currState, getRole());
		int counter = 0;
		int num_moves = legalMoves.size();
		List<List<Integer> > scores = new ArrayList<List<Integer> >();
		for(int i = 0; i<num_moves; i++){
			scores.add(new ArrayList<Integer>());
		}
		while(true){
			if(System.currentTimeMillis() >= _timeout) {
				int index = calculateBest(scores);
				System.out.println(counter);
				return legalMoves.get(index);
			}
			int path_score = -1;
			try {
				path_score = random_simulation(currState, legalMoves,counter%num_moves);
			} catch (TransitionDefinitionException e) {
				e.printStackTrace();
			} catch (GoalDefinitionException e) {
				e.printStackTrace();
			}
			//if(path_score==-1)
			scores.get(counter%num_moves).add(path_score);
			counter++;
			//System.out.println(counter);
		}
	}

	private int random_simulation(MachineState currState, List<Move> legalMoves, int i) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException {
		MachineState tempState = getStateMachine().getRandomNextState(currState, getRole(), legalMoves.get(i));
		while(true){
			if(getStateMachine().isTerminal(tempState)){
				return(getStateMachine().getGoal(tempState, getRole()));
			}
			tempState = getStateMachine().getRandomNextState(tempState);
		}
//		return generator.nextInt(101);

		//return 0;
	}

	private int calculateBest(List<List<Integer>> scores) {
		int a = 4;
		int b = a+1;
		List<Double> score_average = new ArrayList<Double>();
		for(int i=0; i<scores.size(); i++){
			score_average.add(average_score(scores.get(i)));
		}
		int index = 0;
		double best_score = 0;
		for(int i = 0; i<score_average.size(); i++){
			if(score_average.get(i)>best_score){
				index = i;
				best_score = score_average.get(i);
			}
			System.out.println(score_average.get(i));
		}
		return index;
	}

	private Double average_score(List<Integer> score) {
		double sum = 0;
		for(int i = 0; i<score.size(); i++){
			sum+= score.get(i);
		}
		return sum/score.size();
	}

	private Move_Node getValue(MachineState currState) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		if(System.currentTimeMillis() >= _timeout) return new Move_Node(0,null);
		List<Move> legalMoves = getStateMachine().getLegalMoves(currState, getRole());
		Move_Node best_node = new Move_Node(-1,null); 
		for(int i=0; i<legalMoves.size(); i++){
			List<List<Move> > jointMoves = getStateMachine().getLegalJointMoves(currState, getRole(), legalMoves.get(i));
			int value_worstcase = MAX_SCORE;
			for(int j=0; j<jointMoves.size(); j++){
				MachineState tempState = getStateMachine().getNextState(currState, jointMoves.get(j));
				int currvalue;
				if(getStateMachine().isTerminal(tempState)){
					//System.out.println("hey");
					currvalue = getStateMachine().getGoal(tempState, getRole());
				} else if(_cache.containsKey(tempState)){
					currvalue = _cache.get(tempState);
				} else {
					currvalue = getValue(tempState).value;
					if(System.currentTimeMillis() >= _timeout) return best_node;
					_cache.put(tempState, currvalue);
				}
				if(currvalue<value_worstcase) {
					value_worstcase = currvalue;
				}
			}
			if(best_node.value<value_worstcase) {
				best_node.value = value_worstcase;
				best_node.move = legalMoves.get(i);
			}
		}

		return best_node;		
	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

}
package player.gamer.statemachine;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;

import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;

public class TheEliminator extends HeuristicGamer {
	private static int LOOK_AHEAD = 1;

	@Override
	public double getHeuristic(MachineState state, long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		List<Double > weights = Arrays.asList(1.0, 0.0, 0.0, 10.0);
		List<Double > features = mobilityHeuristics(state);
		//if(features.get(4) == 0) return 0;
		//if(features.get(4) == 100) return 1000000;

		double value = 0;
		for(int i = 0; i < weights.size(); i++){
			value += weights.get(i) * features.get(i);
		}		
		return value;
	}
	/*
	 * returns a list in this order:
	 * array[0] = playermobility
	 * array[1] = playerfocus
	 * array[2] = oppmobility
	 * array[3] = oppfocus
	 */
	private List<Double > mobilityHeuristics(MachineState state) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{

		HashSet<MachineState > reachable = new HashSet<MachineState >();
		//first, add this state
		reachable.add(state);
		//next, expand it, to see how many states are reachable after that
		for(int i = 0; i < LOOK_AHEAD; i++){
			if(System.currentTimeMillis() > _stopTime) break;
			HashSet<MachineState > oldReachable = new HashSet<MachineState>(reachable);
			reachable = new HashSet<MachineState >();
			//expand each state in oldReachable
			for(MachineState currState : oldReachable){
				if(!getStateMachine().isTerminal(currState))
					reachable.addAll(getStateMachine().getNextStates(currState));
			}
		}
		double numOppMoves = 0;
		double numPlayerMoves = 0;
		double goalPoints = -1;
		for(MachineState currState : reachable){
			if(!getStateMachine().isTerminal(currState)){
				numPlayerMoves += getStateMachine().getLegalMoves(currState, getRole()).size();
				List<Role > roles = getStateMachine().getRoles();
				for(Role role : roles){
					if(role != getRole())
						numOppMoves += getStateMachine().getLegalMoves(currState, role).size();
				}
			}
			else goalPoints = getStateMachine().getGoal(currState, getRole());
			//else goalPoints = 	getRelGoal(state);
		}
		List<Double > heurs = new ArrayList<Double >();
		heurs.addAll(Arrays.asList(numPlayerMoves, 1/numPlayerMoves, numOppMoves, 1/numOppMoves, goalPoints));
		return heurs;
	}





	private int _count = 0;

	@Override
	public List<Double> getHeuristicPOST(MachineState state, long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {

		List<List<Double>> MC_List = new ArrayList<List<Double> >();
		List<Boolean> Eliminated = new ArrayList<Boolean>();
		List<Move> legalMoves = getStateMachine().getLegalMoves(getCurrentState(), getRole());
		for(int i=0; i<legalMoves.size(); i++){
			MC_List.add(new ArrayList<Double>());
			Eliminated.add(false);
		}
		int count = 0;
		int numMoves = legalMoves.size();

		long curr_time = System.currentTimeMillis();
		long time_step = (timeout-curr_time)/numMoves;

		int numEliminated = 0;

		_levelsToExpand = 3;
		List<Double> quickMiniMax = getMovePOST(getCurrentState(), timeout, legalMoves);
		for(int i = 0; i<quickMiniMax.size(); i++){
			System.out.println("i: " +i+ "score: " + quickMiniMax.get(i));
			if(quickMiniMax.get(i)==101){
				List<Double> MC_Scores = new ArrayList<Double>();
				for(int j=0; j<numMoves; j++){
					MC_Scores.add(0.0);
				}
				MC_Scores.set(i, 100.0);
				return MC_Scores;
			}
			if(quickMiniMax.get(i)==-101){
				numEliminated++;
				Eliminated.set(i, true);
				MC_List.get(i).add(0.0);
			} else if (quickMiniMax.get(i)!=0.0){
				numEliminated++;
				Eliminated.set(i, true);
				MC_List.get(i).add(quickMiniMax.get(i));
			}

		}

		curr_time = System.currentTimeMillis();

		time_step = (timeout-curr_time)/numMoves;


		while(true){
			if(System.currentTimeMillis()>timeout) {
				System.out.println("WHOOPS");
				break;
			}
			if(System.currentTimeMillis()>curr_time + (numEliminated+2)*time_step){
				numEliminated++;
				double worstscore = 100;
				int index = 0;
				for(int i = 0; i<numMoves; i++){
					if(Eliminated.get(i)) continue;
					double score = average_score(MC_List.get(i));
					if(score<worstscore){
						worstscore = score;
						index = i;
					}
				}
				Eliminated.set(index, true);
				System.out.println("eliminated index: " + index + " score: " +worstscore + "  size: "+ MC_List.get(index).size());
				continue;
			}

			if(Eliminated.get(count%numMoves)){
				count++;
				continue;
			}

			double MC_value = MonteCarlo(state,0, legalMoves.get(count%numMoves)); 
			MC_List.get(count%numMoves).add(MC_value);
			count++;
		}
		List<Double> MC_Scores = new ArrayList<Double>();
		for(int i = 0; i<MC_List.size(); i++){
			MC_Scores.add(average_score(MC_List.get(i)));
		}
		for(int i = 0; i<MC_List.size(); i++){
			if(!Eliminated.get(i)){
				System.out.println("NOT eliminated index: " + i + " score: " +MC_Scores.get(i) + "  size: "+ MC_List.get(i).size());

			}
		}
		return MC_Scores;
		//return 0;
	}



	private double MonteCarlo(MachineState state, long timeout, Move move) throws GoalDefinitionException, TransitionDefinitionException, MoveDefinitionException {
		List<Double> scores = new ArrayList<Double>();



		while(true){
			MachineState tempState = state;


			while(true){				
				if(getStateMachine().isTerminal(tempState)){
					double tempscore = getStateMachine().getGoal(tempState, getRole());
					//double tempscore =  getRelGoal(tempState);
					scores.add(tempscore);
					break;
				}
				tempState = getStateMachine().getNextStateDestructively(tempState, getStateMachine().getRandomJointMove(tempState));
				//tempState = getStateMachine().getRandomNextState(tempState);
			}
			if(System.currentTimeMillis() >= timeout) return average_score(scores);

		}
	}

	private Double average_score(List<Double> score) {
		if(score.isEmpty()) {
			//System.out.println("no time!!");
			return 0.0;
		}
		double sum = 0;
		for(int i = 0; i<score.size(); i++){
			sum+= score.get(i);
		}
		_count++;
		//System.out.print("count: "+_count);
		//System.out.println(" scorsize: " + score.size());
		return sum/score.size();
	}





	@Override
	public String getName() {
		return "Wacky:The-Dominator-Combinator-Eliminator";
	}








}
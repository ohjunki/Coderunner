import java.io.BufferedWriter;
import java.io.FileWriter;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Scanner;

public class Comvine2 {

	
	private static boolean holeFlag=false;
	static int ama=0;
    /*
     * Sizes of the game field
     */
    private static final int FIELD_COLUMN_COUNT = 25;
    private static final int FIELD_ROW_COUNT = 16;

    /*
     * Values of cells
     */
    private static final char REMOVED_BRICK = '-';
    private static final char LADDER = 'H';
    private static final char BRICK = '=';
    private static final char EMPTY = '.';
    private static final char GOLD = '*';
    private static int term = 0;

    /*
     * Contains previous positions used by BFS
     */
    private static Position prevPosition[][] = new Position[FIELD_ROW_COUNT][FIELD_COLUMN_COUNT];

    /*
     * Contains previous moves used by BFS
     */
    private static Move prevMove[][] = new Move[FIELD_ROW_COUNT][FIELD_COLUMN_COUNT];

    /*
     * The game field
     */
    private static char[][] field = new char[FIELD_ROW_COUNT][FIELD_COLUMN_COUNT];
    private static char[][] fieldForSearch = new char[FIELD_ROW_COUNT][FIELD_COLUMN_COUNT];
    private static int[][] golds = new int[FIELD_ROW_COUNT][FIELD_COLUMN_COUNT];
    private static char[] brickOverGold; 
    private static Golder[] goldmember;
    private static Position[] brickForBreaking;
    private static int mapGoldcount =0;
    private static boolean digdag=false;
    private static Move firstDirection = null;
    private static int targetGold=-1;

    /*
     * Position queue used by BFS
     */
    private static Queue<Position> queue = new LinkedList<Position>();

    /*
     * Programs of the enemies
     */
    private static String[] enemyPrograms;

    /*
     * Positions of the enemies
     */
    private static Position[] enemies;
    private static Position[] prevEnemies;
    private static Position[] prevprevEnemies;

    /*
     * Masters of the enemies
     */
    private static int[] masterOfEnemy;

    /*
     * Positions of the runners, our runner is on the first place
     */
    private static Position[] runners;

    /*
     * Some information about the runners
     */
    private static int[] scores;
    private static int[] delays;

    /*
     * Scanner used for data reading
     */
    private static Scanner in;

    /*
     * Entry point of player
     */
   /*
    * Enemy near runner position information
    */
   private static Position[] posi;

   /*
    * Check runner on LADDER
    */
   private static boolean LADDER_FLAG;
   public static FileWriter fw; 

    public static boolean isLand() {
        if (getCell(posi[7]) == BRICK) {
            return true;
        }
        if (getCell(posi[7]) == REMOVED_BRICK) {
            for (Position e : enemies) {
                if (posi[7].equals(e)) {
                    return true;
                }
            }
        }
        return false;
    }

    public static boolean isTop() {
        if (!canGo(posi[1])) {
            return true;
        }
        return false;
    }

    public static int getDistance(Position p1, Position p2) {
        return (p1.getRow() - p2.getRow() + p1.getColumn() - p2.getColumn());
    }

    public static boolean isNearEnemy(Position p) {

        for (Position e : enemies) {
            if (p.equals(e) && getCell(p) != REMOVED_BRICK) {
                return true;
            }
            if (p.shift(Move.LEFT).equals(e)
                    && getCell(p.shift(Move.LEFT)) != REMOVED_BRICK) {
                return true;
            }
            if (p.shift(Move.RIGHT).equals(e)
                    && getCell(p.shift(Move.RIGHT)) != REMOVED_BRICK) {
                return true;
            }
            if (p.shift(Move.BOTTOM).equals(e)
                    && getCell(p.shift(Move.BOTTOM)) != REMOVED_BRICK) {
                return true;
            }
            if (p.shift(Move.TOP).equals(e)
                    && getCell(p.shift(Move.TOP)) != REMOVED_BRICK) {
                return true;
            }
        }

        return false;
    }

    public static Move onLadder(Move gold) {
      Move mtg = gold;
      Move rtg = reverseMove(mtg);
      int rtgE = isNearEnemy(rtg);
      int mtgE = isNearEnemy(mtg);
      int LeftE = isNearEnemy(Move.LEFT);
      int RightE = isNearEnemy(Move.RIGHT);
      int TopE = isNearEnemy(Move.TOP);
      int BottomE = isNearEnemy(Move.BOTTOM);
      Position mt = moveDirection(mtg);

      // 가는 방향에 적이 없을 때
      if (mtgE == 0) {
         // 가는 방향으로 갈 수 없음
         if (!canGo(moveDirection(mtg))) {
            Position next = queue.peek();
            if (mt.row > next.row) {
               mtg = Move.TOP;
            } else if (mt.row < next.row) {
               mtg = Move.BOTTOM;
            } else if (mt.column > next.column) {
               mtg = Move.LEFT;
            } else {
               mtg = Move.RIGHT;
            }
            mtgE = isNearEnemy(mtg);
            rtg = reverseMove(mtg);
            rtgE = isNearEnemy(rtg);
         }

         else {
            // 가는 방향으로 갈 수 있음
            if (mtgE == 0) {
               // 밑으로 갈 때
               if (getCell(moveDirection(mtg)) == LADDER)
                  return mtg;
               // 밑에 뛸 수 있음
               else if (LandOkay(mt, Landing(mt))) {
                  return mtg;
               }
               // 밑에 뛸 수 없음
               else {
                  if (isNearEnemy(posi[1]) && canGo(posi[1]))
                     return Move.TOP;
               }
            }

            return mtg;
         }
      }

      /****** 가는 방향에 적이 있음 ******/
      if ((mtg.equals(Move.TOP)||(mtg.equals(Move.BOTTOM)) && isEnemy(moveDirection(mtg)))) {
         if (canGo(posi[3]) && LandOkay(posi[3], Landing(posi[3]))) {
            return Move.LEFT;
         } else if (canGo(posi[5]) && LandOkay(posi[5], Landing(posi[5]))) {
            return Move.RIGHT;
         }
      }
      // 반대 방향으로 갈 수 있음
      if (canGo(moveDirection(rtg))) {
         // 반대 방향에 적이 없음
         if (rtgE == 0)
            return rtg;
         // 반대 방향에 적이 있음
         else {
            // 위아래 모두 적이 있음
            if (rtg.equals(Move.BOTTOM) || rtg.equals(Move.TOP)) {
               return Jump(gold);
            }
            // 좌우 모두 적이 있음
            // 위에 적이 있음
            if (TopE != 0) {
               // 아래에 적이 있음
               if (BottomE != 0) {
                  return mtg;
               }
               // 아래로 내려갈 수 있음
               if (canGo(moveDirection(Move.BOTTOM))) {
                  return Move.BOTTOM;
               }
               // 아래로 내려갈 수 없음
               // 왼쪽적이 더 멀리
               if (LeftE > RightE) {
                  return Move.DIG_RIGHT;
               }
               // 오른쪽 적이 더 멀리
               else {
                  return Move.DIG_LEFT;
               }
            }
            // 위에 적이 없음
            // 위로 갈 수 있음
            if (canGo(moveDirection(Move.TOP))) {
               return Move.TOP;
            }
            // 위로 갈 수 없음
            // 아래에 적이 있음
            if (BottomE != 0) {
               return mtg;
            }
            // 아래로 내려갈 수 있음
            if (canGo(moveDirection(Move.BOTTOM))) {
               return Move.BOTTOM;
            }
            // 아래로 내려갈 수 없음
            return mtg;
         }
      }
      // 반대 방향으로 갈 수 없음
      else {
         // 위아래로 이동할 수 없음
         if (mtg.equals(Move.BOTTOM) || mtg.equals(Move.TOP)) {
            return Jump(gold);
         }
         // 좌우로 이동할 수 없음
         // 위에 적이 있음
         if (TopE != 0) {
            // 아래 적이 있음 || 아래로 못감
            if (BottomE != 0 || canGo(moveDirection(Move.BOTTOM))) {
               // 왼쪽에 무적
               if (LeftE == 0) {
                  return Move.DIG_RIGHT;
               }
               // 오른쪽에 무적
               if (RightE == 0) {
                  return Move.DIG_LEFT;
               }
               // 왼쪽 적이 더 가까움
               if (LeftE < RightE) {
                  return Move.DIG_LEFT;
               }
               // 오른쪽 적이 더 가까움
               else {
                  return Move.DIG_RIGHT;
               }
            }
            // 아래 적이 없음
            return Move.BOTTOM;
         }
         // 위에 적이 없음
         if (canGo(moveDirection(Move.TOP))) {
            return Move.TOP;
         }
         // 위로 이동할 수 없음
         // 아래 적이 있음 || 아래로 못감
         if (BottomE != 0 || canGo(moveDirection(Move.BOTTOM))) {
            // 왼쪽에 무적
            if (LeftE == 0) {
               return Move.DIG_RIGHT;
            }
            // 오른쪽에 무적
            if (RightE == 0) {
               return Move.DIG_LEFT;
            }
            // 왼쪽 적이 더 가까움
            if (LeftE < RightE) {
               return Move.DIG_LEFT;
            }
            // 오른쪽 적이 더 가까움
            else {
               return Move.DIG_RIGHT;
            }
         }
         // 아래 적이 없음
         return Move.BOTTOM;
      }
   }

    public static int isNearEnemy(Move m) {

        int dir1 = 0, dir2 = 0, dir3 = 0, dir4 = 0;
        int subdir1 = 0, subdir2 = 0;
        int dist = 0;
        int flag = 0;

        switch (m) {
        case BOTTOM:
            dir1 = 7;
            dir2 = 10;
            if (getCell(posi[6]) != REMOVED_BRICK && !isEnemyin(posi[0])) {
                subdir1 = 6;
            } else {
                subdir1 = dir2;
            }
            if (getCell(posi[8]) != REMOVED_BRICK && !isEnemyin(posi[0])) {
                subdir2 = 8;
            } else {
                subdir2 = dir2;
            }
            flag = 4;
            break;
        case LEFT:
            dir1 = 3;
            dir2 = 11;
            if (getCell(posi[0]) != REMOVED_BRICK && !isEnemyin(posi[0]))
                subdir1 = 0;
            else
                subdir1 = dir2;
            if (getCell(posi[6]) != REMOVED_BRICK && !isEnemyin(posi[6]))
                subdir2 = 6;
            else
                subdir2 = dir2;
            break;
        case RIGHT:
            dir1 = 5;
            dir2 = 12;
            if (getCell(posi[2]) != REMOVED_BRICK && !isEnemyin(posi[2]))
                subdir1 = 2;
            else
                subdir1 = dir2;
            if (getCell(posi[8]) != REMOVED_BRICK && !isEnemyin(posi[8]))
                subdir2 = 8;
            else
                subdir2 = dir2;
            break;
        case TOP:
            dir1 = 1;
            dir2 = 9;
            subdir1 = 0;
            subdir2 = 2;
            flag = 3;
            break;
        }

        for (Position e : enemies) {
            if (posi[dir1].equals(e)) {
                if (getCell(posi[dir1]) != REMOVED_BRICK) {
                    dist = 1;
                    break;
                }
            }
            if (posi[dir2].equals(e)) {
                if (getCell(posi[dir2]) != REMOVED_BRICK) {
                    dist = 2;
                }
            }
            if (posi[subdir1].equals(e)) {
                if (getCell(posi[subdir1]) != REMOVED_BRICK) {
                    dist = 2;
                }
            }
            if (posi[subdir2].equals(e)) {
                if (getCell(posi[subdir2]) != REMOVED_BRICK) {
                    dist = 2;
                }
            }
        }
        if (LADDER_FLAG && dist != 0) {
            switch (flag) {
            case 3:
                dir3 = 0;
                dir4 = 2;
                break;
            case 4:
                dir3 = 6;
                dir4 = 8;
                break;
            }
            if (flag != 0) {
                for (Position e : enemies) {
                    if (posi[dir3].equals(e)) {
                        if (getCell(posi[dir3]) != REMOVED_BRICK) {
                            dist = 2;
                            break;
                        }
                    }
                    if (posi[dir4].equals(e)) {
                        if (getCell(posi[dir1]) != REMOVED_BRICK) {
                            dist = 2;
                            break;
                        }
                    }
                }
            }
        }

        return dist;
    }

   public static boolean isEnemy(Position p){
      for(Position e : enemies){
         if(p.equals(e)){
            return true;
         }
      }
      return false;
   }

   public static Move reverseMove(Move m) {
      if (m == Move.LEFT) {
         return Move.RIGHT;
      } else if (m == Move.RIGHT) {
         return Move.LEFT;
      } else if (m == Move.TOP) {
         return Move.BOTTOM;
      } else if (m == Move.BOTTOM) {
         return Move.TOP;
      } else {
         return Move.NONE;
      }
   }
    public static boolean LandOkay(Position p, int index) {
        Position tmp = new Position(p.getRow() + index - 1, p.getColumn());
        Position[] isE = new Position[2];

        // if (!isEmptyLike(getCell(tmp.shift(Move.BOTTOM)))) {
        // return false;
        // }

        isE[0] = new Position(tmp.getRow(), tmp.getColumn() - ((index - 1) / 2));
        isE[1] = new Position(tmp.getRow(), tmp.getColumn() + ((index - 1) / 2));

        for (int i = 0; i < 2; i++) {
            // if (isNearEnemy(isE[i])) {
            // return false;
            // }
            for (Position e : enemies) {
                if (isE[i].equals(e)) {
                    return false;
                }
            }
        }
        return true;
    }


    private static boolean canGo(Position cell) {
        return !(cell.row < 0) && !(cell.column < 0)
                && !(cell.column >= FIELD_COLUMN_COUNT)
                && !(cell.row >= FIELD_ROW_COUNT) && isEmptyLike(getCell(cell))
                || getCell(cell) == LADDER || getCell(cell) == GOLD;
    }
    
        private static boolean isEnemyin(Position p) {
        if (getCell(p) == REMOVED_BRICK) {
            for (Position e : enemies) {
                if (p.equals(e)) {
                    return true;
                }
            }
        }
        return false;
    }

    private static Position moveDirection(Move m) {
        Position toGo;
        switch (m) {
        case BOTTOM:
            toGo = posi[7];
            break;
        case LEFT:
            toGo = posi[3];
            break;
        case RIGHT:
            toGo = posi[5];
            break;
        case TOP:
            toGo = posi[1];
            break;
        default:
            toGo = new Position(-1, -1);
            break;
        }
        return toGo;
    }

    public static Move Jump(Move gold) {
        int left_landing;
        boolean left_flag;
        int left;
        int right_landing;
        boolean right_flag;
        int right;

        Move mtg = gold;
        Move rtg = reverseMove(gold);
        Position toGo = moveDirection(mtg);
        Position reversetoGo = moveDirection(rtg);

        if (isEmptyLike(getCell(posi[3]))) { // left
                                                // empty
            left_landing = Landing(posi[3]);
            left_flag = LandOkay(posi[3], left_landing);
            left = isNearEnemy(Move.LEFT);
        } else { // left brick
            left_landing = 0;
            left_flag = false;
            left = 0;
        }
        if (isEmptyLike(getCell(posi[5]))) { // right
                                                // empty
            right_landing = Landing(posi[5]);
            right_flag = LandOkay(posi[5], right_landing);
            right = isNearEnemy(Move.RIGHT);
        } else { // right brick

            right_flag = false;
            right_landing = 0;
            right = 0;
        }
        if ((mtg.equals(Move.TOP)||(mtg.equals(Move.BOTTOM)) && isEnemy(moveDirection(mtg)))) {
                 if (canGo(posi[3]) && LandOkay(posi[3], Landing(posi[3]))) {
                    return Move.LEFT;
                 } else if (canGo(posi[5]) && LandOkay(posi[5], Landing(posi[5]))) {
                    return Move.RIGHT;
                 }
              }
        if (left_landing == 0 && right_landing == 0) {
            if (isNearEnemy(mtg) > isNearEnemy(rtg)
                    && !(inthetrick(mtg) && (mtg.equals(Move.LEFT) || mtg
                            .equals(Move.RIGHT)))) {
                return mtg;
            } else if (canGo(reversetoGo)
                    && !(inthetrick(rtg) && (mtg.equals(Move.LEFT) || mtg
                            .equals(Move.RIGHT)))) {
                return rtg;
            }
        }

        if (left_landing == 1 && right_landing == 1) {
            if (left == 0) {
                if (right == 0) {
                    return mtg;
                } else if (canGo(posi[3])) {
                    return Move.LEFT;
                }
            } else if (right == 0 && canGo(posi[5])) {
                return Move.RIGHT;
            }

            if (left == 1) {
                if (canDig(Move.RIGHT))
                    return Move.DIG_RIGHT;
                return Move.RIGHT;
            } else {
                if (canDig(Move.LEFT))
                    return Move.DIG_LEFT;
                if (isNearEnemy(mtg) > isNearEnemy(rtg)) {
                    return mtg;
                } else if (canGo(reversetoGo)) {
                    return rtg;
                }
            }
        } else if (left_landing == 1) {
            if (left == 0 && !inthetrick(Move.LEFT)) {
                if (mtg.equals(Move.RIGHT)
                        && LandOkay(posi[5], Landing(posi[5]))) {
                    return mtg;
                }
                return Move.LEFT;
            } else if ((left == 1 || left == 2) && canDig(Move.LEFT)) {
                return Move.DIG_LEFT;
            } else {
                if (right_flag && !inthetrick(Move.RIGHT)) {
                    return Move.RIGHT;
                }
                if (isNearEnemy(gold) == 2) {
                    return mtg;
                }
                if (isNearEnemy(reverseMove(gold)) == 2
                        && canGo(reversetoGo)
                        && !(inthetrick(rtg) && (mtg.equals(Move.LEFT) || mtg
                                .equals(Move.RIGHT)))) {
                    return rtg;
                }
                return Move.RIGHT;
            }
        } else if (right_landing == 1) {
            if (right == 0 && !inthetrick(Move.RIGHT)) {
                if (mtg.equals(Move.LEFT)
                        && LandOkay(posi[3], Landing(posi[3]))) {
                    return mtg;
                }
                return Move.RIGHT;
            } else if ((right == 1 || right == 2) && canDig(Move.RIGHT)) {
                return Move.DIG_RIGHT;
            } else {
                if (left_flag && !inthetrick(Move.LEFT)) {
                    return Move.LEFT;
                }
                if (isNearEnemy(gold) == 2
                        && !(inthetrick(mtg) && (mtg.equals(Move.LEFT) || mtg
                                .equals(Move.RIGHT)))) {
                    return mtg;
                }
                if (isNearEnemy(reverseMove(gold)) == 2
                        && canGo(reversetoGo)
                        && !(inthetrick(rtg) && (mtg.equals(Move.LEFT) || mtg
                                .equals(Move.RIGHT)))) {
                    return rtg;
                }
                return Move.LEFT;
            }
        } else {
            if (left_flag) {
                if (right_flag) {
                    if (left_landing > right_landing && !inthetrick(Move.RIGHT)) {
                        return Move.RIGHT;
                    } else {
                        if (!inthetrick(Move.LEFT)) {
                            return Move.LEFT;
                        }
                    }
                }

                if (mtg == Move.LEFT) {
                    if (getCell(posi[6]) == BRICK)
                        return Move.DIG_LEFT;
                    if (canGo(moveDirection(rtg))) {
                        return rtg;
                    }
                        if (isNearEnemy(posi[1])) {
                            return Move.BOTTOM;
                        }
                    return Move.TOP;
                }
                return mtg;
            } else {
                if (right_flag && canGo(moveDirection(Move.RIGHT))) {
                    return Move.RIGHT;
                }
                if (isNearEnemy(gold) == 2
                        && !(inthetrick(rtg) && (mtg.equals(Move.LEFT) || mtg
                                .equals(Move.RIGHT)))) {
                    return mtg;
                }
                if (canGo(reversetoGo)) {
                    return rtg;
                }
            }
        }

        return Move.NONE;
    }

    public static int Landing(Position p) {
        for (int i = 0; i < 16; i++) {
            Position tmp = new Position(p.getRow() + i, p.getColumn());
            for (Position e : enemies) {
                if (getCell(tmp) == BRICK
                        || (getCell(tmp) == REMOVED_BRICK && tmp.equals(e))) {
                    return i;
                }
            }
        }
        return 0;
    }

    private static Move EnemyDirection(int enemyindex){
        if(enemies[enemyindex].getColumn()>runners[0].getColumn()){
            return Move.RIGHT;
        }else if(enemies[enemyindex].getColumn()<runners[0].getColumn()){
            return Move.LEFT;
        }else if(enemies[enemyindex].getRow()<runners[0].getRow()){
            return Move.TOP;
        }else if(enemies[enemyindex].getRow()>runners[0].getRow()){
            return Move.BOTTOM;
        }else{
            return Move.NONE;
        }
    }

    private static boolean ContinueGold(int LeftEnemy ,int RightEnemy,int TopEnemy,int BottomEnemy,Move gold ){
        if( LeftEnemy != -1 && gold == Move.LEFT )
            return false;
        if( RightEnemy != -1 && gold == Move.RIGHT)
            return false;
        if( TopEnemy != -1 && gold == Move.TOP)
            return false;
        if( BottomEnemy != -1 && gold == Move.BOTTOM)
            return false;
        return true;
    }


    public static void main(String[] args) {
        try {
            in = new Scanner(System.in);

            // Read initial state of the world
            int turns = in.nextInt();
            readFirstDescription();

            // Pass through turns
            for(int turnIndex = 0; turnIndex < turns; turnIndex++) {
                int turn = in.nextInt();
                if (turn == -1) {
                    break;
                }
                // Read the current state of the world and make a move
               
                readStateDescription();
                int m;
                Move move=makeMove();
                if(inthetrick(move)){
                	if(getCell(runners[0].shift(Move.BOTTOM))!=BRICK)
                		move=Move.BOTTOM;
                	else
                		move=Move.TOP;
        	    }
                System.out.println(move);
                System.out.flush();
            }
        } catch (Exception e) {
        	e.printStackTrace(System.err);
            System.err.println(e.getMessage());
            System.exit(-1);
        }
    }
    private static boolean in1Distance(Move direction){
        Position position=runners[0].shift(direction);
        boolean isEnemy=false;
        
        for(int i=0;i<enemies.length;i++){
            Position enemy=enemies[i];
            if(enemy.getRow()==position.getRow()
                    &&enemy.getColumn()==position.getColumn()){
                isEnemy = true;
                break;
            }
        }
        return isEnemy;
    }
    private static Move isNeedDig( Move gold){
        if( brickForBreaking[targetGold] == null )
            return gold;

        // if( targetGold == -1)
        //     System.err.println("dam");
        Position temp;
        int right=-1, left=-1, bottom=-1;
            for( int i=0; i<mapGoldcount; i++){
                if ( brickForBreaking[i] != null)
                    if( i == targetGold || (brickForBreaking[i].getRow() == brickForBreaking[targetGold].getRow() && Math.abs( brickForBreaking[i].getColumn() - brickForBreaking[targetGold].getColumn() ) <= 1 ) )  
                                if( brickForBreaking[i].equals(runners[0].shift(Move.RIGHT).shift(Move.BOTTOM))  ){
                        // if(getCell(brickForBreaking[i] ) == BRICK ){
                                right=i;
                                continue;
                    }

                if ( brickForBreaking[i] != null ) 
                    if( ( i == targetGold
                 ||(brickForBreaking[i].getRow()==brickForBreaking[targetGold].getRow() && Math.abs( brickForBreaking[i].getColumn() - brickForBreaking[targetGold].getColumn() ) <= 1  ) ) )
                    if( brickForBreaking[i].equals(runners[0].shift(Move.LEFT).shift(Move.BOTTOM)) ){
                    // if(  getCell(brickForBreaking[i] ) == BRICK ){
                        left=i;
                        continue;
                    }
                if( brickForBreaking[i] != null && ( i == targetGold
                 ||(brickForBreaking[i].getRow()==brickForBreaking[targetGold].getRow() && Math.abs( brickForBreaking[i].getColumn() - brickForBreaking[targetGold].getColumn() ) <= 1  ) )  && brickForBreaking[i].equals( runners[0].shift(Move.BOTTOM))  ){
                    // if( getCell(brickForBreaking[i] ) == BRICK ){
                        bottom = i;
                        continue;
                    }
            }

            switch(right){
                case -1:
                    switch(left){
                        case -1:
                            switch(bottom){
                                case -1:
                                    return gold;
                                default:
                                    if( getCell( runners[0].shift(Move.RIGHT).shift(Move.BOTTOM) ) == BRICK ){
                                        if( !in1Distance(Move.RIGHT) && in2Distance(Move.RIGHT) == -1)
                                            return Move.RIGHT;
                                        else if(!in1Distance(Move.LEFT) && in2Distance(Move.LEFT) == -1)
                                            return Move.LEFT;
                                        else
                                            return Move.RIGHT;
                                    }else if( getCell( runners[0].shift(Move.LEFT).shift(Move.BOTTOM) ) == BRICK){
                                        if(!in1Distance(Move.LEFT) && in2Distance(Move.LEFT) == -1)
                                            return Move.LEFT;
                                        else
                                            return Move.RIGHT;
                                    }
                            }
                        break;
                        default:
                                if( canDig(Move.LEFT) )
                                    return Move.DIG_LEFT;
                                else 
                                    return Move.LEFT;

                        }
                default:
                    if( canDig(Move.RIGHT))
                        return Move.DIG_RIGHT;
                    else  
                        return Move.RIGHT;
            }
     }
    /*
	 * Calculates the next move for our runner
	 */
	private static Move makeMove() {
        digdag= false;
        firstDirection=null;

	    if (!runners[0].correct()) {
	        return Move.NONE;
	    }

        /// shimgun code
         posi = new Position[13];
          for (int i = 0; i < 9; i++) {
             posi[i] = new Position(runners[0].getRow() - 1 + i / 3,
                   runners[0].getColumn() - 1 + i % 3);
          }

          posi[9] = new Position(runners[0].getRow() - 2, runners[0].getColumn());
          posi[10] = new Position(runners[0].getRow() + 2, runners[0].getColumn());
          posi[11] = new Position(runners[0].getRow(), runners[0].getColumn() - 2);
          posi[12] = new Position(runners[0].getRow(), runners[0].getColumn() + 2);

          LADDER_FLAG = false;
          if (getCell(runners[0]) == LADDER)
             LADDER_FLAG = true;

          Move goldTemp = moveToGoldWithBreak(10);
         if( goldTemp == null)
            goldTemp = moveToEarlyGold(0); 
          else if( delays[0] == 0){
               firstDirection = isNeedDig( goldTemp );
               if( firstDirection != goldTemp ){
                    digdag = true;
                    if( goldTemp == Move.BOTTOM ){
                        if(firstDirection != Move.DIG_LEFT && firstDirection != Move.DIG_RIGHT  )
                            goldTemp = firstDirection;
                        else{
                            if( runners[0].shift(Move.RIGHT).shift(Move.RIGHT).equals( move( runners[0].shift(Move.RIGHT) , Move.RIGHT)))
                                goldTemp = Move.RIGHT;
                            else
                                goldTemp = Move.LEFT;  // checking
                        }
                    } else if( firstDirection != Move.DIG_LEFT && firstDirection != Move.DIG_RIGHT )
                        goldTemp = firstDirection;
               }
         }
         else{
            goldTemp = moveToGoldWithoutBreak(10);
         }
         // firstDirection = isNeedDig( goldTemp );
         // if( firstDirection != goldTemp ){
         //        digdag = true;
         //    if( delays[0] == 0 ){
         //        if( goldTemp == Move.BOTTOM ){
         //                if(firstDirection != Move.DIG_LEFT && firstDirection != Move.DIG_RIGHT  )
         //                    goldTemp = firstDirection;
         //                else{
         //                    if( runners[0].shift(Move.RIGHT).shift(Move.RIGHT).equals( move( runners[0].shift(Move.RIGHT) , Move.RIGHT)))
         //                        goldTemp = Move.RIGHT;
         //                    else
         //                        goldTemp = Move.LEFT;  // checking
         //                }
         //            } else if( firstDirection != Move.DIG_LEFT && firstDirection != Move.DIG_RIGHT )
         //                goldTemp = firstDirection;
         //    }
         //    else
         //        goldTemp = moveToGoldWithoutBreak(10 );
         // }
         if( goldTemp == Move.DIG_RIGHT || goldTemp == Move.DIG_LEFT)
            System.err.println("big end");
          //here can occuer
         if (LADDER_FLAG) {
            if( getCell( runners[0].shift(Move.BOTTOM)) == BRICK && digdag ) 
            {
                if( firstDirection == Move.DIG_RIGHT )
                {
                    if( !in1Distance(Move.TOP) ){
                        if( in2Distance(Move.TOP) == -1 ){
                            if( !in1Distance(Move.LEFT) ){
                                if(!in1Distance(Move.RIGHT) && ( in2Distance(Move.RIGHT) == -1 || willEnemyMove(in2Distance(Move.RIGHT)) ) )
                                    return firstDirection;
                                else
                                    return whereToRun(Move.RIGHT);    // more specific
                            }else
                                    return Move.TOP;
                        }
                        else{
                            if( !in1Distance(Move.LEFT) ){
                                if(!in1Distance(Move.RIGHT) && ( in2Distance(Move.RIGHT) == -1 || willEnemyMove(in2Distance(Move.RIGHT)) ) )
                                    return firstDirection;
                                else
                                    return Move.RIGHT;    // more specific
                            }else
                                    return Move.RIGHT;
                        }
                    }
                    else
                    {
                        if( !in1Distance(Move.RIGHT) && in2Distance(Move.RIGHT) == -1 )
                            return Move.RIGHT;
                        else
                            return Move.LEFT;
                    }

                }
                else if(  firstDirection == Move.DIG_LEFT ){
                    if( !in1Distance(Move.TOP) ){
                        if( in2Distance(Move.TOP) == -1 ){
                            if( !in1Distance(Move.RIGHT) ){
                                if(!in1Distance(Move.LEFT) && ( in2Distance(Move.LEFT) == -1 || willEnemyMove(in2Distance(Move.LEFT)) ) )
                                    return firstDirection;
                                else
                                    return whereToRun(Move.LEFT);    // more specific
                            }else
                                    return Move.TOP;
                        }
                        else{
                            if( !in1Distance(Move.RIGHT) ){
                                if(!in1Distance(Move.LEFT) && ( in2Distance(Move.LEFT) == -1 || willEnemyMove(in2Distance(Move.LEFT)) ) )
                                    return firstDirection;
                                else
                                    return Move.LEFT;    // more specific
                            }else
                                    return Move.LEFT;
                        }
                    }
                    else
                    {
                        if( !in1Distance(Move.LEFT) && in2Distance(Move.LEFT) == -1 )
                            return Move.LEFT;
                        else
                            return Move.RIGHT;
                    }

                }
                else
                    System.err.println("errererer");
            }
            else                
             return onLadder(goldTemp);
         } else {
                // System.err.println("here"+ama++);
	   /// shimgun code 
///////////////////////////////////////////////////////////////////////////
        	     boolean isEnemy=false;
        	     Move gold = goldTemp;
        	     int closestEnemy=in2Distance(gold);
        	     int LeftEnemy=-1,RightEnemy=-1 , TopEnemy= -1 , BottomEnemy = -1; 
                 
                int closestEnemyCount =0;
                for(int i=0;i<enemies.length;i++){

                        if(runners[0].getColumn()-1==enemies[i].getColumn()&&runners[0].getRow()==enemies[i].getRow() && LeftEnemy == -1 ){
                            LeftEnemy=i;
                            closestEnemyCount++;
                        }else if(runners[0].getColumn()+1==enemies[i].getColumn()&&runners[0].getRow()==enemies[i].getRow() && RightEnemy == -1){
                            RightEnemy=i;
                            closestEnemyCount++;
                        }else if ( runners[0].getColumn() == enemies[i].getColumn() && runners[0].getRow()-1 == enemies[i].getRow() && TopEnemy == -1 ){
                            TopEnemy=i;
                            closestEnemyCount++;
                        } else if ( runners[0].getColumn() == enemies[i].getColumn() && runners[0].getRow()+1 == enemies[i].getRow() && BottomEnemy == -1 ){
                            if( getCell( enemies[i] ) == REMOVED_BRICK )
                                continue;
                            BottomEnemy=i;
                            closestEnemyCount++;
                        }
                 }

        	       if(closestEnemy!=-1 || closestEnemyCount > 0){
                	    	// if(twoenemy(gold)){
                          	    	// 	for(int i=0;i<enemies.length;i++){
                	    	// 		Position enemy=enemies[i];
                	    	// 		if(enemy.getRow()==runners[0].getRow()
                	    	// 				&&enemy.getColumn()==runners[0].getColumn()
                	           	// 				&&getCell(enemy)!=REMOVED_BRICK){
                	    	// 			isEnemy=true;
                	    	// 		}
                	    	// 	}
                	    	// 	if(getCell(runners[0].shift(Move.RIGHT))!=BRICK && !isEnemy){
                	    	// 		return  Move.RIGHT;
                	    	// 	}
                	    	// }
                	    	Move opposite=whereToRun(gold);
                	    	if(canDig(gold)){
                                 if(LeftEnemy!=-1 ){
                                     if(willEnemyMove(LeftEnemy)){
                                                   return Move.RIGHT;
                                     }else{return Move.DIG_LEFT;}
                                   }else if(RightEnemy!=-1){
                                      if(willEnemyMove(RightEnemy)){
                                       return Move.LEFT;
                                     }else{return Move.DIG_RIGHT;}
                                               }else{
                               //if(거리 2)바로 뚫기
                               //****************************
                               if(opposite==Move.LEFT)return Move.DIG_RIGHT;
                                   else if(opposite==Move.RIGHT)return Move.DIG_LEFT;
                               }

                            } else{

                                int row ;
                                int column ;
                                if( LeftEnemy == -1 && RightEnemy == -1 && TopEnemy == -1 && BottomEnemy == -1 ){
                                    return Move.NONE;
                                } else if( LeftEnemy != -1 || RightEnemy != -1){
                                    if( ContinueGold(LeftEnemy , RightEnemy, TopEnemy, BottomEnemy, gold) )
                                        return gold;
                                    if( gold == Move.LEFT){
                                        if ( LeftEnemy != -1)
                                        {
                                            boolean subflag=true; 
                                            if( getCell( enemies[LeftEnemy].shift(Move.BOTTOM) ) == REMOVED_BRICK ){
                                                for(int i=0; i< enemies.length ; i++){
                                                    if( enemies[i].equals(enemies[LeftEnemy].shift(Move.BOTTOM) ))
                                                        subflag = false;
                                                }
                                                if(subflag == true)
                                                    if( in2Distance( Move.LEFT ) == -1 || !willEnemyMove(in2Distance(Move.LEFT)) )
                                                        return Move.LEFT;
                                            }
                                            if(RightEnemy != -1)
                                            {
                                                // if(TopEnemy != -1 && !move(runners[0] , Move.BOTTOM).equals(runners[0]))
                                                //     return Move.BOTTOM;
                                                // else if( BottomEnemy != -1 &&  !move(runners[0] , Move.TOP).equals(runners[0]) )
                                                //     return Move.TOP;
                                                // else
                                                //     return Move.RIGHT;
                                                return Move.BOTTOM;
                                            } else

                                            row =enemies[LeftEnemy].getRow();
                                            column=  enemies[LeftEnemy].getColumn();
                                            opposite = Move.RIGHT;
                                             if( !move(runners[0] , opposite ).equals( runners[0]) && move(runners[0].shift(Move.RIGHT) , Move.BOTTOM ).equals(runners[0].shift(Move.RIGHT)) )
                                                  return Move.RIGHT;
                                            else if( getCell(new Position(row+1 , column ) )== LADDER && 
                                                ( !in1Distance(Move.BOTTOM) ) ) 
                                                return Move.BOTTOM;
                                            else if( getCell(new Position(row+1 , column )  ) == REMOVED_BRICK ){
                                                for(int i=0;i<enemies.length;i++){
                                                    Position enemy=enemies[i];
                                                    if(enemy.getRow()==row+1
                                                            && enemy.getColumn()==column)
                                                        return opposite;
                                                }
                                            }
                                            return opposite;
                                        } else {
                                            opposite = Move.LEFT;
                                            row =enemies[RightEnemy].getRow();
                                            column =  enemies[RightEnemy].getColumn();

                                             if( !move(runners[0] , opposite).equals( runners[0]) && move(runners[0].shift(Move.LEFT) , Move.BOTTOM ).equals(runners[0].shift(Move.LEFT)) )
                                                  return Move.LEFT;
                                            else if( getCell(new Position(row+1 , column )) == LADDER ) 
                                                return Move.BOTTOM;
                                            else if( getCell(new Position(row+1 , column )  ) == REMOVED_BRICK ){
                                                for(int i=0;i<enemies.length;i++){
                                                    Position enemy=enemies[i];
                                                    if(enemy.getRow()==row+1
                                                            && enemy.getColumn()==column)
                                                        return opposite;
                                                }
                                            }
                                            return opposite;
                                        }
                                    }else{
                                        if ( RightEnemy != -1)
                                        {
                                            boolean subflag=true;
                                            if( getCell( enemies[RightEnemy].shift(Move.BOTTOM) ) == REMOVED_BRICK ){
                                                for(int i=0; i< enemies.length ; i++){
                                                    if( enemies[i].equals(enemies[RightEnemy].shift(Move.BOTTOM) ))
                                                        subflag = false;
                                                }
                                                if(subflag == true)
                                                    return Move.RIGHT;
                                            }

                                            if(LeftEnemy != -1)
                                            {
                                                if(TopEnemy != -1 && !move(runners[0] , Move.BOTTOM).equals(runners[0]))
                                                    return Move.BOTTOM;
                                                else if( BottomEnemy != -1 &&  !move(runners[0] , Move.TOP).equals(runners[0]) )
                                                    return Move.TOP;
                                                else
                                                    return Move.LEFT;
                                            }
                                            row =enemies[RightEnemy].getRow();
                                            column=  enemies[RightEnemy].getColumn();
                                            opposite = Move.LEFT;

                                             if( !move(runners[0] , opposite).equals( runners[0]) && move(runners[0].shift(Move.LEFT) , Move.BOTTOM ).equals(runners[0].shift(Move.LEFT)) )
                                                  return Move.LEFT;
                                            else if( getCell(new Position(row+1 , column ) )== LADDER ) 
                                                return Move.BOTTOM;
                                            else if( getCell(new Position(row+1 , column )  ) == REMOVED_BRICK ){
                                                for(int i=0;i<enemies.length;i++){
                                                    Position enemy=enemies[i];
                                                    if(enemy.getRow()==row+1
                                                            && enemy.getColumn()==column)
                                                        return opposite;
                                                }
                                            }
                                            return opposite;
                                        }else {
                                            opposite = Move.RIGHT;
                                            row =enemies[LeftEnemy].getRow();
                                            column =  enemies[LeftEnemy].getColumn();

                                             if( !move(runners[0] , opposite).equals( runners[0]) && move(runners[0].shift(Move.RIGHT) , Move.BOTTOM ).equals(runners[0].shift(Move.RIGHT)) )
                                                  return Move.RIGHT;
                                            else if( getCell(new Position(row+1 , column )) == LADDER ) 
                                                return Move.BOTTOM;
                                            else if( getCell(new Position(row+1 , column )  ) == REMOVED_BRICK ){
                                                for(int i=0;i<enemies.length;i++){
                                                    Position enemy=enemies[i];
                                                    if(enemy.getRow()==row+1
                                                            && enemy.getColumn()==column)
                                                        return opposite;
                                                }
                                            }
                                            return opposite;
                                        }

                                    }
                                   
                                 }else{
                                    if( TopEnemy != -1 ){
                                        if( getCell( runners[0].shift( Move.BOTTOM) ) != LADDER ){
                                            if( RightEnemy == -1 ){
                                                if( in2Distance(Move.RIGHT) == -1 )
                                                    return Move.RIGHT;
                                                else if( !willEnemyMove(in2Distance(Move.RIGHT))) 
                                                    return Move.RIGHT;
                                                else if( delays[0] == 0)
                                                    return Move.RIGHT;
                                            }
                                            if( LeftEnemy == -1 ){
                                                if( in2Distance(Move.LEFT) == -1 )
                                                    return Move.LEFT;
                                                else if( !willEnemyMove(in2Distance(Move.RIGHT))) 
                                                    return Move.LEFT;
                                                if( delays[0] == 0)
                                                    return Move.LEFT;
                                            }
                                            if( getCell( runners[0].shift( Move.BOTTOM) ) == EMPTY )
                                                return Move.BOTTOM;
                                            else
                                                return Move.TOP;
                                        }
                                        else
                                        {
                                            return Move.LEFT;
                                        }
                                    }
                                    if( BottomEnemy != -1 ){
                                        if( getCell( runners[0] ) != LADDER ){
                                            if( RightEnemy == -1 ){
                                                if( in2Distance(Move.RIGHT) == -1 )
                                                    return Move.RIGHT;
                                                else if( !willEnemyMove(in2Distance(Move.RIGHT))) 
                                                    return Move.RIGHT;
                                                if( delays[0] == 0)
                                                    return Move.RIGHT;
                                            }
                                            if( LeftEnemy == -1 ){
                                                if( in2Distance(Move.LEFT) == -1 )
                                                    return Move.LEFT;
                                                else if( !willEnemyMove(in2Distance(Move.RIGHT))) 
                                                    return Move.LEFT;
                                                if( delays[0] == 0)
                                                    return Move.LEFT;
                                            }
                                            return Move.RIGHT;
                                        }
                                    }
                                }
                            }
        	    } else if(runners[0].getRow()==runners[1].getRow() && runners[1].getRow()==FIELD_ROW_COUNT-2 && Math.abs(runners[0].getColumn()-runners[1].getColumn())<3)
                    {

                            if(gold==Move.RIGHT &&runners[0].getColumn()<runners[1].getColumn()){
                                return Move.DIG_RIGHT;
                            }else if(gold==Move.LEFT &&runners[0].getColumn()>runners[1].getColumn()){
                                return Move.DIG_LEFT;
                            }
                    }else{

                        int row=runners[0].getRow();
                        boolean noLadder=true;
                        for(char c:field[row])
                            if(c==LADDER){
                                noLadder=false;
                                break;
                            }
                        if(row==FIELD_ROW_COUNT-2 && noLadder)
                        {
                            boolean dosuicide = true;
                            for(int x=0; x< mapGoldcount ; x++ )
                                if( goldmember[x].getPosition().getRow() == FIELD_ROW_COUNT-2){
                                    if( goldmember[x].delays < 15)
                                    {
                                        dosuicide = false;
                                        break;
                                    }
                                }
                            if( dosuicide)
                                return suicide();
                        }
                        else if(gold != Move.NONE){
                            if(digdag){
                                return firstDirection;
                            }
                            else{

                                if ( gold == Move.RIGHT && !runners[0].shift( gold).equals( move( runners[0].shift(gold), Move.BOTTOM)) )
                                {   
                                    return checking(gold);
                                }else if  ( gold == Move.LEFT && !runners[0].shift( gold).equals( move( runners[0].shift(gold), Move.BOTTOM))){ //if(  gold == Move.LEFT && getCell(runners[0].shift( gold).shift(Move.BOTTOM)) == EMPTY ){
                                    return checking(gold);
                                }
                                return  gold;
                            }
            	       }
                        // return moveToGoldWithBreak(4);
                }

            }
            // if we jump to the Empty air , will be alive?
                    return moveToEarlyGold(0);
	}
	
     private static Move checking( Move direct){
            Position startFlyPosition = runners[0].shift( direct);
            int countingLength = 1;
            while(countingLength != 0){
                if(  !isEmptyLike( getCell(startFlyPosition.shift(Move.BOTTOM)) )  )
                 break;
                else{
                    countingLength++;
                    startFlyPosition = startFlyPosition.shift(Move.BOTTOM);
                }
            }
            System.err.println( " startFlyPosition Row"+startFlyPosition.getRow() + " column = "+startFlyPosition.getColumn() + " Cell = "+getCell(startFlyPosition));
            int[] enemytemp = new int[6];
            int eneCount=0;

            ///// somting chek
            boolean onlyOneway = false;
            Position RightTemp = startFlyPosition.shift(Move.RIGHT);
            Position LeftTemp = startFlyPosition.shift(Move.LEFT);

            for(int i=0; i<2 ; i++)
            {
                if( getCell(RightTemp) == BRICK || isEmptyLike(getCell(RightTemp.shift(Move.BOTTOM))) )
                {
                    System.err.println( " RightTemp Row"+RightTemp.getRow() + " column = "+RightTemp.getColumn() + " Cell = "+getCell(RightTemp.shift(Move.BOTTOM)));
                    onlyOneway=true;
                    break;
                }
                else
                    RightTemp = RightTemp.shift(Move.RIGHT);

                if( getCell(LeftTemp) == BRICK || isEmptyLike(getCell(LeftTemp.shift(Move.BOTTOM))) )
                {
                    onlyOneway=true;
                    break;
                }
                else
                    LeftTemp = LeftTemp.shift(Move.LEFT);
            }
            // if( countingLength <= 2 )
                System.err.println( countingLength );
            if( onlyOneway){
                for( int i=0; i<enemies.length ; i++){
                    if( enemies[i].getRow() == startFlyPosition.getRow() && Math.abs( startFlyPosition.getColumn() - enemies[i].getColumn() ) < countingLength )
                        enemytemp[eneCount++] = i;
                }
                if( eneCount == 0)
                    return direct;
                else
                    return Move.NONE;
            }else{
                for( int i=0; i<enemies.length ; i++){
                    if( enemies[i].getRow() == startFlyPosition.getRow() && Math.abs( startFlyPosition.getColumn() - enemies[i].getColumn() ) < countingLength )
                        enemytemp[eneCount++] = i;
                }
            }
            if( countingLength > 8  )
                return direct;

            if( eneCount == 0)
                return direct;
            else {
                int min = Math.abs( startFlyPosition.getColumn() - enemies[enemytemp[0]].getColumn() );
                for( int i=1 ; i< eneCount ; i++){
                    if( min > Math.abs( startFlyPosition.getColumn() - enemies[enemytemp[i]].getColumn() ) )
                        min = Math.abs( startFlyPosition.getColumn() - enemies[enemytemp[i]].getColumn() ) ; 
                }
                if( min != 0)
                    if( delays[0] - countingLength - (2*min-1) < 1 )
                        return direct;
            }


     //////////////////////////////////////////////////////////////////////
            Position temp;

            for( int i=0; i<eneCount ; i++){
                temp = startFlyPosition;
                Position target = enemies[enemytemp[i]];
                if( !willEnemyMove(enemytemp[i])){
                    if( target.getColumn() - prevEnemies[enemytemp[i]].getColumn() == 1 ){ // right
                        for( int j=0; j<countingLength/2  ; j++)
                            target = target.shift(Move.RIGHT);
                        // right=true;
                    }
                    else
                        for( int j=0; j<countingLength/2  ; j++)
                            target = target.shift(Move.LEFT);
                } else{ 
                    if(  prevEnemies[enemytemp[i]].getColumn() - prevprevEnemies[enemytemp[i]].getColumn() == 1 ){
                        for( int j=0; j<countingLength/2 ; j++)
                            target = target.shift(Move.RIGHT);
                        // right=true;
                    }
                    else
                        for( int j=0; j<countingLength/2 ; j++)
                            target = target.shift(Move.LEFT);
                }
                
                boolean right=false, left =false;
                if( target.getColumn() - runners[0].getColumn() > 0 )
                    right= true;
                else
                    left = true;

                if( right){
                    for(int j=0; j<4 ; j++)
                        if( target.equals(temp) ){
                            switch(j){
                                case 0:
                                case 1:
                                    return Move.NONE;
                                case 2:
                                    if( delays[0]-countingLength >= 3 )
                                        return Move.NONE;
                                case 3: 
                                    if( delays[0]-countingLength >= 5 )
                                        return Move.NONE;
                            }
                        }
                        else
                            temp = temp.shift(Move.RIGHT);
                }else{
                    for(int j=0; j<4 ; j++)
                        if( target.equals(temp) ){
                            switch(j){
                                case 0:
                                case 1:
                                    return Move.NONE;
                                case 2:
                                    if( delays[0]-countingLength >= 3 )
                                        return Move.NONE;
                                case 3: 
                                    if( delays[0]-countingLength >= 5 )
                                        return Move.NONE;
                            }
                        } else
                            temp = temp.shift(Move.LEFT);
                }
            }
            return direct;
    }

	private static Move suicide(){
		if(holeFlag){
			if(getCell(runners[0])==REMOVED_BRICK){
				holeFlag=false;
				return Move.NONE;
			}
			if(getCell(runners[0].shift(Move.RIGHT).shift(Move.BOTTOM))==REMOVED_BRICK){
				return Move.RIGHT;
			}else{
				return Move.LEFT;
			}
		}else{
			if(canDig(Move.RIGHT)){
				holeFlag=true;
				return Move.DIG_RIGHT;
			}else if(canDig(Move.LEFT)){
				holeFlag=true;
				return Move.DIG_LEFT;
			}else{
				return Move.RIGHT;
			}
		}
	}
	
	private static boolean inthetrick(Move move){
		if(getCell(runners[0].shift(Move.RIGHT))==REMOVED_BRICK
				&& move==Move.RIGHT){
			return true;
		}
		
		else if(getCell(runners[0].shift(Move.LEFT))==REMOVED_BRICK
				&& move==Move.LEFT){
			return true;
		}
		return false;

    }//»ç´Ù¸® ¿·¿¡ Àû ºüÁ® ÀÖÀ»‹š (º®µ¹·Î Ãë±Þ)

	
	
    private static Move whereToRun(Move enemyDirection){

        	Move opposite=Move.LEFT;
        	if(enemyDirection==Move.LEFT){
        		if(getCell(runners[0].shift(Move.RIGHT))!=BRICK){
        			opposite=Move.RIGHT;
        		}else{
        			if(getCell(runners[0])==LADDER){
        				opposite=Move.TOP;
        			}else if(getCell(runners[0].shift(Move.BOTTOM))==LADDER){
        				opposite=Move.BOTTOM;
        			}
        		}
        	}
        	else if(enemyDirection==Move.RIGHT){
        		if(getCell(runners[0].shift(Move.LEFT))!=BRICK){
        			opposite=Move.LEFT;
        		}else{
        			if(getCell(runners[0])==LADDER){
        				opposite=Move.TOP;
        			}else if(getCell(runners[0].shift(Move.BOTTOM))==LADDER){
        				opposite=Move.BOTTOM;
        			}
        		}
        	}
        	else if(enemyDirection==Move.BOTTOM){
        		if(!move(runners[0],Move.TOP).equals(runners[0])){
        			opposite=Move.TOP;
        		}else{
        			if(getCell(runners[0].shift(Move.RIGHT))==BRICK)opposite=Move.LEFT;
        			else opposite=Move.RIGHT;
        		}
        	}
        	else if(enemyDirection==Move.TOP){
        		if(!move(runners[0],Move.BOTTOM).equals(runners[0])){
        			opposite=Move.BOTTOM;
        		}else{
        			if(getCell(runners[0].shift(Move.RIGHT))==BRICK)opposite=Move.LEFT;
        			else opposite=Move.RIGHT;
        		}
        	}else{
        		opposite=Move.RIGHT;
        	}
        	return opposite;
    }

    private static int in2Distance(Move direction){
        	Position nextPosition=runners[0].shift(direction);

    		boolean isEnemy=false;
    		
        	for(Move move:Move.values()){
        		Position nextNextPosition=nextPosition.shift(move);
        		for(int i=0;i<enemies.length;i++){
        			Position enemy=enemies[i];
        			if(enemy.getRow()==nextNextPosition.getRow()
        					&&enemy.getColumn()==nextNextPosition.getColumn()
        					&&getCell(enemy)!=REMOVED_BRICK){
        				return i;
        			}
        		}
        	}
        	return -1;
    }
    private static boolean willEnemyMove(int enemy){
        	if(prevEnemies[enemy].getRow()!=enemies[enemy].getRow()
        			||prevEnemies[enemy].getColumn()!=enemies[enemy].getColumn()){
        		return false;
        	}
        	return true;
    }
    
    private static boolean canDig(Move side){
    	if (runners[0].correct()
    			&&delays[0]==0
    			&&runners[0].getRow()!=FIELD_COLUMN_COUNT-1
    			&&(getCell(runners[0])==LADDER 
    				|| getCell(runners[0].shift(Move.BOTTOM))==LADDER 
    				|| getCell(runners[0].shift(Move.BOTTOM))==BRICK)
    			&&getCell(runners[0].shift(Move.BOTTOM).shift(side))==BRICK
    			&&getCell(runners[0].shift(side))!=BRICK
    			&&getCell(runners[0].shift(side))!=LADDER)
    		return true;
    	else return false;
    	
    }

    private static Move moveToGoldWithBreak(int limitturn){ 
        // Clearing arrays for BFS
        for (int x = 0; x < FIELD_ROW_COUNT; x++) {
            for (int y = 0; y < FIELD_COLUMN_COUNT; y++) {
                prevPosition[x][y] = null;
                prevMove[x][y] = null;
            }
        }
        // BFS
        int accumulate=0;
        int curr=0;
        queue.clear();
        Position[] targetarr = new Position[4] ;
        double[] toTargetTurn = new double[4];
        for (int i=0; i<3; i++){
            targetarr[i]= null;
            toTargetTurn[i]=0;
        }
        int closestgoldcount=0;
        // Start BFS from our runner's position to all cells with gold
        update(runners[0], null, Move.NONE);
        int queueturns =0;
        while (!queue.isEmpty()) {
            Position position = queue.poll();
            for( int i=0; i<mapGoldcount ; i++)
            {
                if ( position.equals(goldmember[i].getPosition()) && goldmember[i].getDelays() <= limitturn  ){
                    if(closestgoldcount == 4)
                        break;
                    targetarr[closestgoldcount] = position;
                    toTargetTurn[closestgoldcount++] = queueturns;
                }
            }
            // Iterate through possible moves in order (LEFT, RIGHT, TOP, BOTTOM)
            for (Move move : Move.values()) {
                Position newPosition = moveWithDig(position, move);
                if(update(newPosition, position, move))
                    accumulate++;
            }
            if(curr == 0){
                curr=accumulate;
                accumulate=0;
                queueturns++;
            }
            else
                curr--;
        }
        Position target = SelectTarget(targetarr , toTargetTurn , closestgoldcount);                    ///////////
        if (target == null) {
            if(limitturn>31)
                return null;
            else
                return moveToGoldWithBreak(limitturn+10);
        }

        for( int i=0; i<mapGoldcount ; i++)
            if( target.equals(goldmember[i].getPosition()))
                targetGold = i;

        return SimplereturnGotoObject(target);
    }


    private static Move moveToGoldWithoutBreak(int limitturn){ 
        // Clearing arrays for BFS
        for (int x = 0; x < FIELD_ROW_COUNT; x++) {
            for (int y = 0; y < FIELD_COLUMN_COUNT; y++) {
                prevPosition[x][y] = null;
                prevMove[x][y] = null;
            }
        }
        // BFS
        queue.clear();
        Position[] targetarr = new Position[4] ;
        double[] toTargetTurn = new double[4];
        for (int i=0; i<3; i++){
            targetarr[i]= null;
            toTargetTurn[i]=0;
        }
        int closestgoldcount=0;
        // Start BFS from our runner's position to all cells with gold
        update(runners[0], null, Move.NONE);
        int queueturns =0;
        int accumulate=0;
        int curr=0;
        while (!queue.isEmpty()) {
            Position position = queue.poll();
            for( int i=0; i<mapGoldcount ; i++)
            {
                if ( position.equals(goldmember[i].getPosition()) && goldmember[i].getDelays() <= limitturn  ){
                    if(closestgoldcount == 4)
                        break;
                    targetarr[closestgoldcount] = position;
                    toTargetTurn[closestgoldcount++] = queueturns;
                }
            }
            // Iterate through possible moves in order (LEFT, RIGHT, TOP, BOTTOM)
            for (Move move : Move.values()) {
                Position newPosition = move(position, move);
                if(update(newPosition, position, move))
                    accumulate++;
            }
            if(curr == 0){
                curr=accumulate;
                accumulate=0;
                queueturns++;
            }
            else
                curr--;

        }


        Position target = SelectTarget(targetarr , toTargetTurn , closestgoldcount);               
        
        // If there is no available gold on the field, then do nothing
        if (target == null) {
            if(limitturn>50)
                return null;
            else
                return moveToGoldWithoutBreak(limitturn+30);
        }

        for( int i=0; i<mapGoldcount ; i++)
            if( target.equals(goldmember[i].getPosition()))
                targetGold = i;

        return SimplereturnGotoObjectwithoutbreaking(target);
    }

    private static Position SelectTarget(Position[] targetarr , double[] toTargetTurn , int closestgoldcount ){
        Position target=null;
        int rounding=0;
        double min = 100000;
        int[] equalRow = new int[4];
        char [][] roundsearch = new char[3][3];

        for(int i=0; i< closestgoldcount ;i++){
            rounding = 1;
                Position temp = targetarr[i];
                int row = temp.getRow();
                int column = temp.getColumn();
                boolean up=false, down=false, left=false, right=false;
                switch(row){
                    case 0:
                        switch(column){
                            case 0:
                                if( field[row][column+1] == GOLD) rounding++;
                                if( field[row+1][column+1] == GOLD) rounding++;
                                if( field[row+1][column-1] == GOLD) rounding++;
                            break;
                            case 24:
                                if( field[row][column-1] == GOLD) rounding++;
                                if( field[row+1][column-1] == GOLD) rounding++;
                                if( field[row+1][column] == GOLD) rounding++;
                            break;
                            default:
                                if( field[row][column+1] == GOLD) rounding++;
                                if( field[row+1][column+1] == GOLD) rounding++;
                                if( field[row][column-1] == GOLD) rounding++;
                                if( field[row+1][column-1] == GOLD) rounding++;
                                if( field[row+1][column] == GOLD) rounding++;
                            
                        }
                    break;
                    case 15:
                        switch(column){
                            case 0:
                                if( field[row-1][column] == GOLD) {
                                    up = true;
                                 rounding++;
                                }
                                if( field[row-1][column+1] == GOLD) rounding++;
                                if( field[row][column+1] == GOLD) rounding++;
                            break;
                            case 24:
                                if( field[row][column-1] == GOLD) rounding++;
                                if( field[row-1][column-1] == GOLD) rounding++;
                                if( field[row-1][column] == GOLD){
                                    up = true;
                                 rounding++;
                                }
                            break;
                            default:
                                if( field[row][column-1] == GOLD) rounding++;
                                if( field[row-1][column-1] == GOLD) rounding++;
                                if( field[row-1][column] == GOLD) {
                                    up = true;
                                 rounding++;
                                }
                                if( field[row-1][column+1] == GOLD) rounding++;
                                if( field[row][column+1] == GOLD) rounding++;
                        }
                    break;
                    default:
                        switch(column){
                            case 0:
                                if( field[row-1][column] == GOLD){
                                    up = true;
                                 rounding++;
                                }
                                if( field[row-1][column+1] == GOLD) rounding++;
                                if( field[row][column+1] == GOLD) rounding++;
                                if( field[row+1][column+1] == GOLD) rounding++;
                                if( field[row+1][column] == GOLD) rounding++;
                            break;
                            case 24:
                                if( field[row-1][column] == GOLD){
                                    up = true;
                                    rounding++;
                                }
                                if( field[row-1][column-1] == GOLD) rounding++;
                                if( field[row][column-1] == GOLD) rounding++;
                                if( field[row+1][column-1] == GOLD) rounding++;
                                if( field[row+1][column] == GOLD) rounding++;
                            break;
                            default:
                                if( field[row-1][column-1] == GOLD) {
                                    rounding++;
                                }
                                if( field[row-1][column] == GOLD){
                                    up = true;
                                    rounding++;
                                }
                                if( field[row-1][column+1] == GOLD){
                                    rounding++;
                                }
                                if( field[row][column+1] == GOLD){
                                    right = true;
                                    rounding++;
                                }
                                if( field[row+1][column+1] == GOLD){
                                    rounding++;
                                }
                                if( field[row][column-1] == GOLD){
                                    left = true;
                                    rounding++;
                                }
                                if( field[row+1][column-1] == GOLD) {
                                    rounding++;
                                }
                                if( field[row+1][column] == GOLD) {
                                    down = true;
                                    rounding++;
                                }
                        }

            }
            if( getCell( targetarr[i].shift(Move.BOTTOM)) != BRICK ){
                if(up){
                    int turns = CountingTurns( targetarr[i].shift(Move.TOP));
                    if( turns != -1 && Math.abs( toTargetTurn[i] - turns) <3 ){
                        targetarr[i] = targetarr[i].shift(Move.TOP);
                        i--;
                        continue;
                    }
                }
            }
                if( targetarr[i].getRow() == runners[0].getRow() )
                //     equalRow[i] = Math.abs( targetarr[i].getcolumn() - runners[0].getColumn())
                // else
                //     equalRow[i] = -1;
                    toTargetTurn[i] /= 2.0;
                    // return targetarr[i];


            if( toTargetTurn[i] == 0)
                continue;
            if( rounding >= 3 )
                rounding++;
            if( min > toTargetTurn[i] / rounding ){
                min = toTargetTurn[i] / rounding;
                target = targetarr[i];
            }
        }
        return target;
    }
    private static Move SimplereturnGotoObject( Position object){
        for (int x = 0; x < FIELD_ROW_COUNT; x++) {
            for (int y = 0; y < FIELD_COLUMN_COUNT; y++) {
                prevPosition[x][y] = null;
                prevMove[x][y] = null;
            }
        }
        queue.clear();
        Position target = null;
        update(runners[0], null, Move.NONE);
        while (!queue.isEmpty()) {
            Position position = queue.poll();
            if (position.equals(object)){
                target = position;
                break;
            }
            // Iterate through possible moves in order (LEFT, RIGHT, TOP, BOTTOM)
            for (Move move : Move.values()) {
                Position newPosition = moveWithDig(position, move);
                 update(newPosition, position, move);       
            }
        }
        if( target == null)
            return null;

        for( int i=0; i<mapGoldcount ; i++)
            if( target.equals(goldmember[i].getPosition()))
                targetGold = i;

        Position current = target, previous = target;
        while (!current.equals(runners[0])) {
            previous = current;
            current = prevPosition[current.getRow()][current.getColumn()];
        }
        return prevMove[previous.getRow()][previous.getColumn()];
    }
    private static Move SimplereturnGotoObjectwithoutbreaking( Position object){
        for (int x = 0; x < FIELD_ROW_COUNT; x++) {
            for (int y = 0; y < FIELD_COLUMN_COUNT; y++) {
                prevPosition[x][y] = null;
                prevMove[x][y] = null;
            }
        }
        queue.clear();
        Position target = null;
        update(runners[0], null, Move.NONE);
        while (!queue.isEmpty()) {
            Position position = queue.poll();
            if (position.equals(object)){
                target = position;
                break;
            }
            // Iterate through possible moves in order (LEFT, RIGHT, TOP, BOTTOM)
            for (Move move : Move.values()) {
                Position newPosition = move(position, move);
                 update(newPosition, position, move);       
            }
        }
        if( target == null)
            return null;

        for( int i=0; i<mapGoldcount ; i++)
            if( target.equals(goldmember[i].getPosition()))
                targetGold = i;

        Position current = target, previous = target;
        while (!current.equals(runners[0])) {
            previous = current;
            current = prevPosition[current.getRow()][current.getColumn()];
        }
        return prevMove[previous.getRow()][previous.getColumn()];
    }

    private static int CountingTurns(Position object){
        for (int x = 0; x < FIELD_ROW_COUNT; x++) {
            for (int y = 0; y < FIELD_COLUMN_COUNT; y++) {
                prevPosition[x][y] = null;
                prevMove[x][y] = null;
            }
        }
        int accumulate = 0, queueturns = 0, curr=0;
        queue.clear();
        Position target = null;
        update(runners[0], null, Move.NONE);
        while (!queue.isEmpty()) {
            Position position = queue.poll();
            if (position.equals(object)){
                target = position;
                break;
            }
            // Iterate through possible moves in order (LEFT, RIGHT, TOP, BOTTOM)
            for (Move move : Move.values()) {
                Position newPosition = moveWithDig(position, move);
                if( update(newPosition, position, move) ){
                    accumulate++;
                }
            }

            if(curr == 0){
                curr=accumulate;
                accumulate=0;
                queueturns++;
            }
            else
                curr--;
        }
        if (target == null) {
            return -1;
        }
        return queueturns;
    }


    private static Move moveToGold(){
    	// Clearing arrays for BFS
        for (int x = 0; x < FIELD_ROW_COUNT; x++) {
            for (int y = 0; y < FIELD_COLUMN_COUNT; y++) {
                prevPosition[x][y] = null;
                prevMove[x][y] = null;
            }
        }
        // BFS
        queue.clear();
        Position target = null;
        // Start BFS from our runner's position to all cells with gold
        update(runners[0], null, Move.NONE);
        while (!queue.isEmpty()) {
            Position position = queue.poll();
            if (getCell(position) == GOLD) {
                target = position;
                break;
            }
            // Iterate through possible moves in order (LEFT, RIGHT, TOP, BOTTOM)
            for (Move move : Move.values()) {
                Position newPosition = move(position, move);
                update(newPosition, position, move);
            }
        }
        // If there is no available gold on the field, then do nothing
        if (target == null) {
            return Move.NONE;
        }
        for( int i=0; i<mapGoldcount ; i++)
            if( target.equals(goldmember[i].getPosition()))
                targetGold = i;
        // Returning back through previous positions from the closest gold
        Position current = target, previous = target;
        while (!current.equals(runners[0])) {
            previous = current;
            current = prevPosition[current.getRow()][current.getColumn()];
        }
        // Make a move to the closest gold
        return prevMove[previous.getRow()][previous.getColumn()];
    }
    
    private static Move moveToEarlyGold(int turns){//

    	// Clearing arrays for BFS
        for (int x = 0; x < FIELD_ROW_COUNT; x++) {
            for (int y = 0; y < FIELD_COLUMN_COUNT; y++) {
                prevPosition[x][y] = null;
                prevMove[x][y] = null;
            }
        }
        // BFS
        queue.clear();
        Position target = null;

        // Start BFS from our runner's position to all cells with gold
        update(runners[0], null, Move.NONE);
        while (!queue.isEmpty()) {
            Position position = queue.poll();
            if (golds[position.getRow()][position.getColumn()]<turns+10
            		&& golds[position.getRow()][position.getColumn()]>=turns
            		&& !runners[0].equals(position)) {
                target = position;
                break;
            }
            // Iterate through possible moves in order (LEFT, RIGHT, TOP, BOTTOM)
            for (Move move : Move.values()) {
                Position newPosition = move(position, move);
                update(newPosition, position, move);
            }
        }
        // If there is no available gold on the field, then do nothing
        if (target == null) {
        	if(turns>151)
            	return Move.NONE;
        	else
        		return moveToEarlyGold(turns+20);
        }
        // Returning back through previous positions from the closest gold
        Position current = target, previous = target;
        while (!current.equals(runners[0])) {
            previous = current;
            current = prevPosition[current.getRow()][current.getColumn()];
        }
        // Make a move to the closest gold
        return prevMove[previous.getRow()][previous.getColumn()];
    }


    private static boolean twoenemy(Move direction){
    	if(direction == Move.TOP){
    			if(getCell(runners[0].shift(Move.BOTTOM))!=BRICK){
    				Position NextPosition=runners[0].shift(Move.BOTTOM);
    				Position nNextPosition=NextPosition.shift(Move.BOTTOM);
    				
    				for(int i=0;i<enemies.length;i++){
    					Position enemy=enemies[i];
    					if(enemy.getRow()==NextPosition.getRow()
    							&&enemy.getColumn()==NextPosition.getColumn()
    							&&getCell(enemy)!=REMOVED_BRICK){
    						return true;
    					}else if(enemy.getRow()==nNextPosition.getRow()
    							&&enemy.getColumn()==nNextPosition.getColumn()
    							&&getCell(enemy)!=REMOVED_BRICK){
    						return true;
    					}
    				}
    			}
    	}else if(direction == Move.BOTTOM){
    		if(getCell(runners[0].shift(Move.TOP))!=BRICK){
    			Position NextPosition=runners[0].shift(Move.TOP);
    			Position nNextPosition=NextPosition.shift(Move.BOTTOM);

    			for(int i=0;i<enemies.length;i++){
    				Position enemy=enemies[i];
    				if(enemy.getRow()==NextPosition.getRow()
    						&&enemy.getColumn()==NextPosition.getColumn()
    						&&getCell(enemy)!=REMOVED_BRICK){
    					return true;
    				}else if(enemy.getRow()==nNextPosition.getRow()
							&&enemy.getColumn()==nNextPosition.getColumn()
							&&getCell(enemy)!=REMOVED_BRICK){
						return true;
					}
    			}
    		}
    	}
    	return false;
    }
    
    private static Position move(Position currentPosition, Move move) {
        
        // Move ignoring trapped enemies
        Position newPosition = moveIgnoringEnemies(currentPosition, move, true);

        // Checks for a enemy below in cell with removed brick
        if (!newPosition.equals(currentPosition) && getCell(newPosition) == REMOVED_BRICK) {
            for (Position enemy : enemies) {
                if (enemy.equals(newPosition)) {
                    // Move without fall down
                    Position position = moveIgnoringEnemies(currentPosition, move, false);
                    if (position.equals(newPosition) && move == Move.BOTTOM) {
                        return currentPosition; // Cannot move below to the cell with enemy
                    } else {
                        return position;
                    }
                }
            }
        }
        return newPosition;
    }


    private static Position moveWithDig(Position currentPosition, Move move) {

        // Move ignoring trapped enemies
        Position newPosition = moveIgnoringEnemiesWithDig(currentPosition, move, true);

        // Checks for a enemy below in cell with removed brick
        if (!newPosition.equals(currentPosition) && getCell(newPosition) == REMOVED_BRICK) {
            for (Position enemy : enemies) {
                if (enemy.equals(newPosition)) {
                    // Move without fall down
                    Position position = moveIgnoringEnemiesWithDig(currentPosition, move, false);
                    if (position.equals(newPosition) && move == Move.BOTTOM) {
                        return currentPosition; // Cannot move below to the cell with enemy
                    } else {
                        return position;
                    }
                }
            }
        }
        return newPosition;
    }

    /*
     * Returns the next position if a one makes the given move from the
     * given position, but ignores enemies in cells with removed bricks
     */
    private static Position moveIgnoringEnemiesWithDig(Position position, Move move, boolean canFly) {
        char currentCell = getCellForSearch(position);
        Position shiftedTopPosition = position.shift(Move.TOP);
        Position shiftedRightPosition = position.shift(Move.RIGHT);
        Position shiftedBottomPosition = position.shift(Move.BOTTOM);
        Position shiftedLeftPosition = position.shift(Move.LEFT);

        // Is flying?
        if (isEmptyLike(currentCell) && isEmptyLike(getCellForSearch(shiftedBottomPosition)) && canFly) {
            return shiftedBottomPosition;
        }
        if (move == Move.NONE) {
            return position;
        }
        switch (move) {
            case TOP:
                if (currentCell == LADDER && getCellForSearch(shiftedTopPosition) != BRICK) {
                    return shiftedTopPosition;
                }
                break;
            case RIGHT:
                if (getCellForSearch(shiftedRightPosition) != BRICK) {
                    return shiftedRightPosition;
                }
                break;
            case BOTTOM:
                if ((currentCell == LADDER || isEmptyLike(currentCell))
                        && (getCellForSearch(shiftedBottomPosition) == LADDER || isEmptyLike(getCellForSearch(shiftedBottomPosition)))) {
                    return shiftedBottomPosition;
                }
                break;
            case LEFT:
                if (getCellForSearch(shiftedLeftPosition) != BRICK) {
                    return shiftedLeftPosition;
                }
                break;
        }
        return position;
    }

    private static Position moveIgnoringEnemies(Position position, Move move, boolean canFly) {
        char currentCell = getCell(position);
        Position shiftedTopPosition = position.shift(Move.TOP);
        Position shiftedRightPosition = position.shift(Move.RIGHT);
        Position shiftedBottomPosition = position.shift(Move.BOTTOM);
        Position shiftedLeftPosition = position.shift(Move.LEFT);

        // Is flying?
        if (isEmptyLike(currentCell) && isEmptyLike(getCell(shiftedBottomPosition)) && canFly) {
            return shiftedBottomPosition;
        }
        if (move == Move.NONE) {
            return position;
        }
        switch (move) {
            case TOP:
                if (currentCell == LADDER && getCell(shiftedTopPosition) != BRICK) {
                    return shiftedTopPosition;
                }
                break;
            case RIGHT:
                if (getCell(shiftedRightPosition) != BRICK) {
                    return shiftedRightPosition;
                }
                break;
            case BOTTOM:
                if ((currentCell == LADDER || isEmptyLike(currentCell))
                        && (getCell(shiftedBottomPosition) == LADDER || isEmptyLike(getCell(shiftedBottomPosition)))) {
                    return shiftedBottomPosition;
                }
                break;
            case LEFT:
                if (getCell(shiftedLeftPosition) != BRICK) {
                    return shiftedLeftPosition;
                }
                break;
        }
        return position;
    }

    private static boolean isEmptyLike(char cell) {
        return cell == EMPTY || cell == GOLD || cell == REMOVED_BRICK ;
    }

    /*
     * Returns cell if the position is inside the game field and BRICK otherwise.
     */
    private static char getCell(Position position) {
        if (0 <= position.getRow() && position.getRow() < FIELD_ROW_COUNT) {
            if (0 <= position.getColumn() && position.getColumn() < FIELD_COLUMN_COUNT) {
                return field[position.getRow()][position.getColumn()];
            }
        
        }
        // The given position is out of the field
        return BRICK;
    }

    private static char getCellForSearch(Position position) {
        if (0 <= position.getRow() && position.getRow() < FIELD_ROW_COUNT) {
            if (0 <= position.getColumn() && position.getColumn() < FIELD_COLUMN_COUNT) {
                return fieldForSearch[position.getRow()][position.getColumn()];
            }
        
        }
        // The given position is out of the field
        return BRICK;
    }
    /*
     * Updates values in BFS
     */
    private static boolean update(Position position, Position prev, Move move) {
        if (prevMove[position.getRow()][position.getColumn()] == null) {
            prevPosition[position.getRow()][position.getColumn()] = prev;
            prevMove[position.getRow()][position.getColumn()] = move;
            queue.add(position);
            return true;
        }
        return false;
    }

    /*
     * Reads per-turn game state
     */
    private static void readStateDescription() {
        // Read the game field
        readGameField();
        if( term != 0)
            term--;
        // Read descriptions of the runners
        for(int i = 0; i < 2; i++) {
            runners[i] = readPosition();
            scores[i] = in.nextInt();
            delays[i] = in.nextInt();
        }

        // Read descriptions of the enemies
        for(int i = 0; i < enemies.length; i++) {
            prevprevEnemies[i]=prevEnemies[i];
        	prevEnemies[i]=enemies[i];
            enemies[i] = readPosition();
            masterOfEnemy[i] = in.nextInt();
        }
    }

    /*
     * Reads one-time world description
     */
    private static void readFirstDescription() {
        // Read the game field
        goldmember = new Golder[40];
        brickForBreaking = new Position[40];
        brickOverGold = new char[40];
        readFirstGameField();
        runners = new Position[2];
        scores = new int[2];
        delays = new int[2];
        // Read descriptions of the runners
        readCharactersPositions(runners);

        // Read descriptions of the enemies
        int enemyCount = in.nextInt();
        prevprevEnemies = new Position[enemyCount];
        prevEnemies=new Position[enemyCount];
        enemies = new Position[enemyCount];
        enemyPrograms = new String[enemyCount];
        masterOfEnemy = new int[enemyCount];
        for (int i = 0; i < enemies.length; i++) {
            enemies[i] = readPosition();
            prevEnemies[i] =null;
            prevprevEnemies[i] = null;
            enemyPrograms[i] = in.next();
        }
    }

    /*
     * Reads the game first field from the scanner
     */

    private static void readFirstGameField() {
        for (int i = 0; i < FIELD_ROW_COUNT; i++) {
            String line = in.next();
        	   field[i] = line.toCharArray();
            for (int j = 0; j < FIELD_COLUMN_COUNT; j++) {
                if(line.charAt(j)==GOLD){
                	golds[i][j]=0;
                }else{
                	golds[i][j]=0xffff;
                }
            }
            for( int j=0; j<FIELD_COLUMN_COUNT ; j++){
                if(line.charAt(j) == GOLD){
                    goldmember[mapGoldcount] = new Golder( i, j, GOLD);
                    goldmember[mapGoldcount].setCurrent(GOLD);
                    goldmember[mapGoldcount++].setPrev(GOLD);
                }
            }
        }
    }
    /*
     * Reads the game field from the scanner
     */
    private static void readGameField() {
        for (int i = 0; i < FIELD_ROW_COUNT; i++) {
            String line = in.next();
        	field[i] = line.toCharArray();
            for (int j = 0; j < FIELD_COLUMN_COUNT; j++) {
                if(line.charAt(j)==GOLD){
                	golds[i][j]=0;
                }else{
                	if(golds[i][j]==0){
                		golds[i][j]=151;
                	}else if(golds[i][j]!=0xffff){
                		golds[i][j]--;
                	}
                }
            }
        }
        for(int i=0; i<mapGoldcount ; i++){
                Position temp = goldmember[i].getPosition();
                if( goldmember[i].getDelays() == 0 ){
                     if( field[temp.getRow()][temp.getColumn()] != GOLD ){
                            goldmember[i].setDelays(150);
                    }
                } else {
                    if(  field[temp.getRow()][temp.getColumn()] == GOLD ){
                            goldmember[i].setDelays(0);
                    }
                    else
                        goldmember[i].setDelays( goldmember[i].getDelays()-1);
                }
                goldmember[i].setCurrent( field[temp.getRow()][temp.getColumn()] );
        }

        for( int i=0; i<mapGoldcount ; i++ ){
                if(goldmember[i].delays != 0){
                    brickForBreaking[i] = null;
                    continue;
                }
                Position PGold = goldmember[i].getPosition();
                Position temp = PGold;
                boolean finding= false;
                while( temp.getRow() > 0 ){
                    if( getCell(temp) == BRICK){
                        finding = true;
                        break;                    
                    }
                    else
                        temp = temp.shift(Move.TOP);
                }
                if( finding ){
                    if( getCell( temp.shift(Move.TOP) ) != LADDER && getCell( temp.shift(Move.TOP) )!=BRICK ){
                        brickForBreaking[i] = temp;
                    }
                    else{
                       brickForBreaking[i] = null;
                    }
                }
                else
                    brickForBreaking[i] = null;
        }

        updateFieldForSearch();
    }
    /*
     * Reads array of positions from the scanner
     */
    private static void  updateFieldForSearch(){
        for( int i=0; i< FIELD_ROW_COUNT ; i++)
            for( int j=0; j< FIELD_COLUMN_COUNT ; j++)
                fieldForSearch[i][j] = field[i][j];


        for ( int i=0; i< mapGoldcount ; i++){
            if( brickForBreaking[i] == null)
                continue;

            // switch( getCell(brickForBreaking[i])){
            //     case BRICK:
                    brickOverGold[i]='~';
                    fieldForSearch[brickForBreaking[i].getRow()][brickForBreaking[i].getColumn()]= EMPTY ;
            //     break;
            //     case REMOVED_BRICK:
            //         boolean existing = false;
            //         for( int j=0 ; j< enemies.length ; j++)
            //         {
            //             if(enemies[j].equals(brickForBreaking[i])){
            //                 existing = true;
            //                 break;
            //             }
            //         }
            //         if( existing)
            //             fieldForSearch[brickForBreaking[i].getRow()][brickForBreaking[i].getColumn()] = BRICK;
            //         else
            //             fieldForSearch[brickForBreaking[i].getRow()][brickForBreaking[i].getColumn()] = EMPTY;
            //     break;
            // }
        }
    }
    private static void readCharactersPositions(Position[] positions) {
        for (int i = 0; i < positions.length; i++) {
            positions[i] = readPosition();
        }
    }

    /*
     * Reads position from the scanner
     */
    private static Position readPosition() {
        int row = in.nextInt();
        int column = in.nextInt();      
        return new Position(row, column);
    }

    /*
     * Class for positions of runners and enemies on the game field
     */
    private static class Golder{
        private Position position ;
        private char prev;
        private char current;
        private int delays=0;

        private Golder( int row, int column , char current ){
            position = new Position(row, column);
            this.current = current;
        }
        public Position getPosition(){
            return position;
        }
        public void setPrev( char prev ){
            this.prev = prev ;
        }
        public void setCurrent( char current ){
            this.current = current ;
        }
        public void setDelays( int delays ){
            this.delays = delays ;
        }

        public char getPrev(){
            return prev;
        }
        public char getCurrent(){
            return current;

        }
        public int getDelays(){
            return delays;
        }
    }
    private static class Position {
        private final int row;
        private final int column;
        private int ifbreak;

        private Position(int row, int column) {
            this.row = row;
            this.column = column;
            ifbreak = 0;
        }

        public int getRow() {
            return row;
        }

        public int getColumn() {
            return column;
        }
        public int getIfbreak(){
            return ifbreak;
        }
        public void setIfbreak( int ifbreak){
            this.ifbreak = ifbreak;
        }

        // Correct position isn't equal to "-1 -1"
        public boolean correct() {
            return row >= 0 && column >= 0;
        }

        // Shift position to specific direction
        public Position shift(Move move) {
            if (move == Move.LEFT) {
                return new Position(row, column - 1);
            }

            if (move == Move.RIGHT) {
                return new Position(row, column + 1);
            }

            if (move == Move.TOP) {
                return new Position(row - 1, column);
            }

            if (move == Move.BOTTOM) {
                return new Position(row + 1, column);
            }

            return new Position(row, column);
        }

        @Override
        public String toString() {
            return "(" + row + ", " + column + ")";
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (!(o instanceof Position)) return false;

            Position position = (Position) o;
            return row == position.row && column == position.column;
        }

        @Override
        public int hashCode() {
            int result = row;
            result = 31 * result + column;
            return result;
        }
    }

    /*
     * Possible moves of runner
     */
    private static enum Move {
        NONE,
        LEFT,
        RIGHT,
        TOP,
        BOTTOM,
        DIG_LEFT,
        DIG_RIGHT
    }
}

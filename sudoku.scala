object sudoku 
{
	val validNums = Array(1,2,3,4,5,6,7,8,9);	
	
	def lfac[E](x : E) : List[E] = List(x)
	def afac[E:ClassManifest](x : E) : Array[E] = Array(x)
	def lappend[E] ( c : List[E] , e : E) : List[E] = e::c
	def aappend[E:ClassManifest] ( c : Array[E] , e : E) : Array[E] = Array(e)++c	
	
	def extract[SC <% Seq[C], C <% Seq[E], E]( nested : SC, factory : (E) => C , append : (C,E) => C ) : C = 
	{ 			
		val seed = nested(0)(0)
		var result : C = factory(seed)
		nested.foreach(_.foreach(a => if(a != seed) result = append(result,a)))		
		result
	} 
	
	def UnnestArray[T:ClassManifest]( state : Array[Array[T]] ) : Array[T] = 
	{
		extract[Array[Array[T]],Array[T],T](state, afac, aappend)					
	}

	def UnnestList[T:ClassManifest]( state : List[List[T]] ) : List[T] = 
	{
		extract[List[List[T]],List[T],T](state, lfac, lappend)					
	}
	
	//if your the only cell in a square that can be one of the valid numbers, then regardless of other
	//possibilities you must be that number
	def OnlyValid(group : Array[cell]) =
	{
		validNums.foreach( num =>
		{
			val couldBeNum = group.filter( arg => arg.m_possible contains num)
			if(couldBeNum.length == 1)
			{
				couldBeNum(0).m_possible = Array(num)
			}
		})
	}

	
	class cell( var m_possible: Array[Int], val m_x: Int, val m_y : Int)
	{		
		var m_squareGroup : Int = -1		
		
		override def toString() : String = Known().toString()		
		
		def Known() : Int = if (m_possible.length == 1) m_possible(0) else 0		
		def ReducePossible( known : Array[Int] )  = if(Known() == 0) m_possible = (m_possible.toSet -- known.toSet).toArray	
		def Knowns( line : Array[cell] ): Array[Int] = line.filter( arg => arg.Known()  != 0).map( arg => arg.Known())
		
		def SquareExclusionReduce(state : Array[Array[cell]]) =
		{
			val squareGroup = UnnestArray[cell](state).filter(arg => arg.m_squareGroup == m_squareGroup)
			
			var identicalPairs : List[List[cell]] = List(List())
			var pairs = squareGroup.filter( arg => arg.m_possible.length == 2)			
			pairs.foreach( a => pairs.foreach(b => if (b != a && b.m_possible.toSet == a.m_possible.toSet) {identicalPairs =  List(a,b)::identicalPairs} ))
						
			identicalPairs = identicalPairs.filter( pair => pair.length == 2)			
			
			if(identicalPairs.length > 0)
			{				
				squareGroup.foreach( arg =>
					{
						
						identicalPairs.foreach( pair => 
						{									
							if(pair(0) != arg && pair(1) != arg) 
							{
								arg.ReducePossible(pair(0).m_possible)
							}
						})
						
					})	
					
				val identicalCoaxialPairs = identicalPairs.filter( pair => pair(0).m_x == pair(1).m_x || pair(0).m_y == pair(1).m_y)
					
				
				List(( a : cell, b : cell)  => a.m_x == b.m_x,( a : cell, b : cell)  => a.m_y == b.m_y).foreach( matchFilter =>
				{					
					identicalCoaxialPairs.foreach( pair => 
					{
						
						if(matchFilter(pair(0),pair(1)))
						{
							UnnestArray[cell](state).filter(arg => matchFilter(arg,pair(0))).foreach( arg =>
							{
								if(arg != pair(0) && arg != pair(1))
								{
									arg.ReducePossible(pair(0).m_possible)
								}
							})
						}						
					})
				})
			}
			
				
			
			//if no cells in your group on other cols (or other rows, but not both) 
			// have any of your possibles, then the other squares on your row/col
			//must not have those numbers in, as the other cells in your square on your row/col
			//must have them			
			List((a :cell, b : cell) => a.m_x == b.m_x, (a :cell, b : cell) => a.m_y == b.m_y).foreach( f =>
			{
				val sameX = squareGroup.filter( a => Possibles(squareGroup.filterNot( b => f(a,b))).toSet.intersect(a.m_possible.toSet).isEmpty)
				if(sameX.length > 0)
				{
					sameX.foreach(sx => UnnestArray[cell](state).filter( arg=> f(arg,sx) && arg.m_squareGroup != sx.m_squareGroup).foreach(_.ReducePossible(sx.m_possible)))
				}
			})		
			
		}
		
		def Possibles( someCells : Array[cell] ) : Array[Int] =
		{
			var result : List[Int] = List()
			for( a <- someCells ) { for( b <- a.m_possible) {result = b::result;}}
			result.toArray
		}

		def ReduceFromGrid( state : Array[Array[cell]]) =
		{
			var reals : List[Int] = List()
			
			val rows = UnnestArray[cell](state).filter(arg => arg.m_x == m_x)
			val cols = UnnestArray[cell](state).filter(arg => arg.m_y == m_y)
			val squares = UnnestArray[cell](state).filter(arg => arg.m_squareGroup == m_squareGroup)		
			
			
			List(rows,cols,squares).foreach(OnlyValid(_))
			List(rows,cols,squares).foreach(a => {reals = reals ++ Knowns(a).toList})			
			ReducePossible(reals.toArray)
			SquareExclusionReduce(state)
		}
		
	}
	
	class grid ( val p : Array[Array[Int]])
	{
		var m_cell : Array[Array[cell]] = Array(Array())		
		def cells() : Array[Array[cell]] = Array.tabulate(p.length,p(0).length)( (i,j) => new cell(if (p(i)(j) == 0) validNums else Array(p(i)(j)) ,i,j) )
				
		def possiblesCount( c : Array[Array[cell]] ) : Int = 
		{
			var count = 0
			c.foreach(_.foreach(count+=_.m_possible.length))
			count
		}		
				
		def ReducePossible()  = 
		{
			m_cell = cells()
			val c = m_cell
			
			Range(0,9,3).foreach( squareY => Range(0,9,3).foreach( squareX => SetSquareId(Range(squareX,squareX+3).map( i => Range(squareY,squareY+3).map( j => c(i)(j)).toArray).toArray) ))								
			var noProgress = 0
			
			while( !solved(c) && noProgress < 3)			
			{	
				val preReducePossible =  possiblesCount(c)
				c.foreach(_.foreach(_.ReduceFromGrid(c)))
				if(preReducePossible == possiblesCount(c))
				{
					noProgress+=1;
				}
				else
				{
					noProgress =0
				}				
			}			
		}
		
		def solved( state : Array[Array[cell]] ) : Boolean = (state.filter(_.filter(arg => arg.Known() == 0).toArray.length != 0).toArray.length)  == 0	
		
		object squareCount 
		{
			var count : Int = 0
		}
		
		def SetSquareId( group : Array[Array[cell]] ) =
		{		
			var trueGroup : List[cell] = UnnestArray[cell](group).toList			
			trueGroup.foreach(arg => arg.m_squareGroup = squareCount.count)
			squareCount.count+=1
			
		}		
	}
	
	def main(args: Array[String]) 
	{
		val puzzle = Array( 
				Array(3,0,0, 9,6,0, 0,0,0),
				Array(1,4,0, 0,0,5, 0,9,0),
				Array(0,0,5, 0,0,0, 0,0,8),
		
				Array(0,0,0, 0,5,0, 0,2,0),
				Array(0,0,3, 8,0,0, 0,1,9),
				Array(0,0,0, 6,4,0, 0,3,0),
		
				Array(0,0,0, 0,0,0, 0,0,1),
				Array(8,0,0, 0,2,0, 0,0,0),
				Array(0,0,1, 0,0,3, 0,0,4)
		)		
		
		val solver = new grid(puzzle);
		solver.cells().foreach(arg => {arg.foreach(print); println("")});
		solver.ReducePossible()
		println("")
		solver.m_cell.foreach(arg => {arg.foreach(print); println("")});
		
	}
}
  
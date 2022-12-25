select
	GroupName, AvgAvgMark
from
	Groups
		left join
			(
				select
					Students.GroupId, avg(AvgMark) as AvgAvgMark
				from
						Students
						left join
							(
								select
									StudentId, avg(cast(Mark as float)) as AvgMark
								from
									Marks
								group by
									StudentId
							) MS
							on (Students.StudentId = MS.StudentId)
				group by
					Students.GroupId
			) GAvg
			on (Groups.GroupId = GAvg.GroupId);
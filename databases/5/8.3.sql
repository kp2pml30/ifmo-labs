select
	GroupName, SumMark
from
	Groups
		left join
			(
				select
					GroupId, sum(Mark) as SumMark
				from
					Students natural join Marks
				group by
					GroupId
			) MS
			on (Groups.GroupId = MS.GroupId);

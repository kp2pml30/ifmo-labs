select
	GroupName, AvgMark
from
	Groups
		left join
			(
				select
					GroupId, avg(cast(Mark as float)) as AvgMark
				from
					Students natural join Marks
				group by
					GroupId
			) MS
			on (Groups.GroupId = MS.GroupId);

select
	SidCid.StudentId,
	count(SidCid.CourseId) as Total,
	count(MarksDistinct.CourseId) as Passed,
	count(SidCid.CourseId) - count(MarksDistinct.CourseId) as Failed
from
	(
		select distinct StudentId, CourseId
		from Students left join Plan on (Students.GroupId = Plan.GroupId)
	) SidCid
	left join (select distinct StudentId, CourseId from Marks) MarksDistinct
		on
			SidCid.StudentId = MarksDistinct.StudentId and
			SidCid.CourseId = MarksDistinct.CourseId
group by
	SidCid.StudentId;
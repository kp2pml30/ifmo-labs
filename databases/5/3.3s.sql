select
	StudentId, StudentName, GroupId
from
	Marks
		natural join Plan
		natural join Students -- or other join to avoid GroupId?
where
	Mark = :Mark and LecturerId = :LecturerId;
update Marks
set
	Mark = coalesce((
		select max(nm.Mark)
		from NewMarks nm
		where
			nm.Mark > Marks.Mark
			and nm.StudentId = Marks.StudentId
			and nm.CourseId = Marks.CourseId
	), Marks.Mark)
where 1 = 1